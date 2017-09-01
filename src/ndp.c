/**
 * Copyright (C) 2012-2013 Steven Barth <steven@midlink.org>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <errno.h>

#include <fcntl.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <net/ethernet.h>
#include <netinet/ip6.h>
#include <netinet/icmp6.h>
#include <netpacket/packet.h>

#include <linux/rtnetlink.h>
#include <linux/filter.h>
#include "router.h"
#include "dhcpv6.h"
#include "ndp.h"



static void handle_solicit(void *addr, void *data, size_t len,
		struct interface *iface, void *dest);
static void handle_rtnetlink(void *addr, void *data, size_t len,
		struct interface *iface, void *dest);
static void catch_rtnetlink(int error);
static void ping_pan(struct uloop_timeout *t);
static void handle_ping_resp(struct uloop_fd *u, unsigned int events);

static uint32_t rtnl_seqid = 0;
static int ping_socket = -1;
static int pan_ping_socket = -1;
static struct odhcpd_event rtnl_event = {{.fd = -1}, handle_rtnetlink, catch_rtnetlink};
static int pan_socket = -1;
static struct uloop_timeout uloop_pan = {.cb = ping_pan};
static struct uloop_fd pan_event = {.fd = -1, .cb = handle_ping_resp};

struct list_head pan_nodes = LIST_HEAD_INIT(pan_nodes);

// Filter ICMPv6 messages of type neighbor soliciation
static struct sock_filter bpf[] = {
	BPF_STMT(BPF_LD | BPF_B | BPF_ABS, offsetof(struct ip6_hdr, ip6_nxt)),
	BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, IPPROTO_ICMPV6, 0, 3),
	BPF_STMT(BPF_LD | BPF_B | BPF_ABS, sizeof(struct ip6_hdr) +
			offsetof(struct icmp6_hdr, icmp6_type)),
	BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, ND_NEIGHBOR_SOLICIT, 0, 1),
	BPF_STMT(BPF_RET | BPF_K, 0xffffffff),
	BPF_STMT(BPF_RET | BPF_K, 0),
};
static const struct sock_fprog bpf_prog = {sizeof(bpf) / sizeof(*bpf), bpf};


// Initialize NDP-proxy
int init_ndp(void)
{
	int val = 256 * 1024;

	// Setup netlink socket
	if ((rtnl_event.uloop.fd = odhcpd_open_rtnl()) < 0)
		return -1;

	if (setsockopt(rtnl_event.uloop.fd, SOL_SOCKET, SO_RCVBUF, &val, sizeof(val)))
		setsockopt(rtnl_event.uloop.fd, SOL_SOCKET, SO_RCVBUFFORCE, &val, sizeof(val));

	// Receive netlink neighbor and ip-address events
	uint32_t group = RTNLGRP_IPV6_IFADDR;
	setsockopt(rtnl_event.uloop.fd, SOL_NETLINK,
			NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));
	group = RTNLGRP_IPV6_ROUTE;
	setsockopt(rtnl_event.uloop.fd, SOL_NETLINK,
			NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));

	odhcpd_register(&rtnl_event);

	// Open ICMPv6 socket
	ping_socket = socket(AF_INET6, SOCK_RAW | SOCK_CLOEXEC, IPPROTO_ICMPV6);
	if (ping_socket < 0) {
		syslog(LOG_ERR, "Unable to open raw socket: %s", strerror(errno));
			return -1;
	}

	val = 2;
	setsockopt(ping_socket, IPPROTO_RAW, IPV6_CHECKSUM, &val, sizeof(val));

	// This is required by RFC 4861
	val = 255;
	setsockopt(ping_socket, IPPROTO_IPV6, IPV6_MULTICAST_HOPS, &val, sizeof(val));
	setsockopt(ping_socket, IPPROTO_IPV6, IPV6_UNICAST_HOPS, &val, sizeof(val));

	// Filter all packages, we only want to send
	struct icmp6_filter filt;
	ICMP6_FILTER_SETBLOCKALL(&filt);
	setsockopt(ping_socket, IPPROTO_ICMPV6, ICMP6_FILTER, &filt, sizeof(filt));

	// Netlink socket, continued...
	group = RTNLGRP_NEIGH;
	setsockopt(rtnl_event.uloop.fd, SOL_NETLINK, NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));

	return 0;
}


static void dump_neigh_table(bool proxy)
{
	struct {
		struct nlmsghdr nh;
		struct ndmsg ndm;
	} req = {
		{sizeof(req), RTM_GETNEIGH, NLM_F_REQUEST | NLM_F_DUMP,
				++rtnl_seqid, 0},
		{.ndm_family = AF_INET6, .ndm_flags = (proxy) ? NTF_PROXY : 0}
	};
	send(rtnl_event.uloop.fd, &req, sizeof(req), MSG_DONTWAIT);
	odhcpd_process(&rtnl_event);
}


int setup_ndp_interface(struct interface *iface, bool enable)
{
	char procbuf[64];
	snprintf(procbuf, sizeof(procbuf), "/proc/sys/net/ipv6/conf/%s/proxy_ndp", iface->ifname);
	int procfd = open(procbuf, O_WRONLY);
	bool dump_neigh = false;

	if (iface->ndp_event.uloop.fd > 0) {
		uloop_fd_delete(&iface->ndp_event.uloop);
		close(iface->ndp_event.uloop.fd);
		iface->ndp_event.uloop.fd = -1;

		if (!enable || iface->ndp != RELAYD_RELAY)
			if (write(procfd, "0\n", 2) < 0) {}

		dump_neigh = true;
	}

	if (enable && (iface->ra == RELAYD_SERVER ||
			iface->dhcpv6 == RELAYD_SERVER || iface->ndp == RELAYD_RELAY)) {
		// Synthesize initial address events
		struct {
			struct nlmsghdr nh;
			struct ifaddrmsg ifa;
		} req2 = {
			{sizeof(req2), RTM_GETADDR, NLM_F_REQUEST | NLM_F_DUMP,
					++rtnl_seqid, 0},
			{.ifa_family = AF_INET6, .ifa_index = iface->ifindex}
		};
		send(rtnl_event.uloop.fd, &req2, sizeof(req2), MSG_DONTWAIT);
	}

	if (enable && iface->ndp == RELAYD_RELAY) {
		if (write(procfd, "1\n", 2) < 0) {}
		close(procfd);

		int sock = socket(AF_PACKET, SOCK_DGRAM | SOCK_CLOEXEC, htons(ETH_P_IPV6));
		if (sock < 0) {
			syslog(LOG_ERR, "Unable to open packet socket: %s",
					strerror(errno));
			return -1;
		}

#ifdef PACKET_RECV_TYPE
		int pktt = 1 << PACKET_MULTICAST;
		setsockopt(sock, SOL_PACKET, PACKET_RECV_TYPE, &pktt, sizeof(pktt));
#endif

		if (setsockopt(sock, SOL_SOCKET, SO_ATTACH_FILTER,
				&bpf_prog, sizeof(bpf_prog))) {
			syslog(LOG_ERR, "Failed to set BPF: %s", strerror(errno));
			return -1;
		}

		struct sockaddr_ll ll = {
			.sll_family = AF_PACKET,
			.sll_ifindex = iface->ifindex,
			.sll_protocol = htons(ETH_P_IPV6),
			.sll_hatype = 0,
			.sll_pkttype = 0,
			.sll_halen = 0,
			.sll_addr = {0},
		};
		bind(sock, (struct sockaddr*)&ll, sizeof(ll));

		struct packet_mreq mreq = {iface->ifindex, PACKET_MR_ALLMULTI, ETH_ALEN, {0}};
		setsockopt(sock, SOL_PACKET, PACKET_ADD_MEMBERSHIP, &mreq, sizeof(mreq));

		iface->ndp_event.uloop.fd = sock;
		iface->ndp_event.handle_dgram = handle_solicit;
		odhcpd_register(&iface->ndp_event);

		// If we already were enabled dump is unnecessary, if not do dump
		if (!dump_neigh)
			dump_neigh_table(false);
		else
			dump_neigh = false;

		if (iface->support_slip)	{

			// Open ICMPv6 socket
			pan_ping_socket = socket(AF_INET6, SOCK_RAW | SOCK_CLOEXEC, IPPROTO_ICMPV6);
			if (pan_ping_socket < 0) {
				syslog(LOG_ERR, "Unable to open raw socket: %s", strerror(errno));
					return -1;
			}

			int val = 2;
			setsockopt(pan_ping_socket, IPPROTO_RAW, IPV6_CHECKSUM, &val, sizeof(val));

			// This is required by RFC 4861
			val = 255;
			setsockopt(pan_ping_socket, IPPROTO_IPV6, IPV6_MULTICAST_HOPS, &val, sizeof(val));
			setsockopt(pan_ping_socket, IPPROTO_IPV6, IPV6_UNICAST_HOPS, &val, sizeof(val));

			// Filter all packages, we only want to send
			struct icmp6_filter filt1;
			ICMP6_FILTER_SETBLOCKALL(&filt1);
			ICMP6_FILTER_SETPASS(ICMP6_ECHO_REPLY, &filt1);
			setsockopt(pan_ping_socket, IPPROTO_ICMPV6, ICMP6_FILTER, &filt1, sizeof(filt1));

			struct ifreq ifr;
    		memset(&ifr, 0, sizeof(ifr));
    		snprintf(ifr.ifr_name, sizeof(ifr.ifr_name), "sl0");

			if (setsockopt(pan_ping_socket, SOL_SOCKET, SO_BINDTODEVICE, (void *)&ifr, sizeof(ifr)))	{
				syslog(LOG_ERR, "Unable to bind the socket to SLIP interface: %s", strerror(errno));
				close(pan_ping_socket);
			}
			else	{
				pan_event.fd = pan_ping_socket;
				uloop_fd_add(&pan_event, ULOOP_READ);

				// Setup netlink socket
				if ((pan_socket = odhcpd_open_rtnl()) < 0)
					syslog(LOG_ERR, "Failed to create to kernel rtnetlink: %s",
									strerror(errno));

				uloop_timeout_set(&uloop_pan,1000);
			}
		}

	} else {
		close(procfd);
	}

	if (dump_neigh)
		dump_neigh_table(true);

	return 0;
}

static void ping_pan(struct uloop_timeout *t)
{
	static uint32_t panrtnl_seq = 0;
	int route_payload_len = 0;
	char dest_addr[INET6_ADDRSTRLEN];
	struct in6_addr binary_dest;


	struct pan_node *node = NULL, *tmp;
	list_for_each_entry_safe(node, tmp, &pan_nodes, head)	{
		if(!node->got_resp && node->destAddr.s6_addr[0])	{
			struct interface *iface = NULL;
			iface = odhcpd_get_interface_by_index(node->ifindex);
			inet_ntop(AF_INET6, &node->destAddr, \
									dest_addr, sizeof(dest_addr));
			syslog(LOG_DEBUG, "deleting route for %s", dest_addr);
			odhcpd_setup_route(&node->destAddr, 128, iface, NULL, 1024, false);
			list_del(&node->head);
		}
	}

	struct req {
		struct nlmsghdr nh;
		struct rtmsg rtm;
	} req = {
		{sizeof(req), RTM_GETROUTE, NLM_F_REQUEST | NLM_F_DUMP, ++panrtnl_seq, 0},
		{AF_INET6, 128, 0, 0, RT_TABLE_MAIN, 0, RT_SCOPE_UNIVERSE, 0, 0},
	};

	if (send(pan_socket, &req, sizeof(req), 0) < 0)
		goto uloop_add;

	uint8_t buf[8192];
	ssize_t len = 0;

	for (struct nlmsghdr *nhm = NULL; ; nhm = NLMSG_NEXT(nhm, len)) {
		while (len < 0 || !NLMSG_OK(nhm, (size_t)len)) {
			len = recv(pan_socket, buf, sizeof(buf), 0);
			nhm = (struct nlmsghdr*)buf;
			if (len < 0 || !NLMSG_OK(nhm, (size_t)len)) {
				if (errno == EINTR)
					continue;
				else
					goto uloop_add;
			}
		}

		if (nhm->nlmsg_type != RTM_NEWROUTE && nhm->nlmsg_type != RTM_DELROUTE)
			break;

		struct rtmsg *route_info;
		struct rtattr *route_dest;
		route_info = (struct rtmsg *) NLMSG_DATA(nhm);
		if (route_info == NULL)	{
			continue;
		}

		route_dest = (struct rtattr *) RTM_RTA(route_info);
		route_payload_len = RTM_PAYLOAD(nhm);
		if (route_dest == NULL)	{
			continue;
		}

		struct interface *iface = NULL;

		for ( ; RTA_OK(route_dest, route_payload_len); \
				route_dest = RTA_NEXT(route_dest, route_payload_len))	{

			if (route_dest->rta_type == RTA_DST)	{
				memcpy(&binary_dest, RTA_DATA(route_dest), sizeof(binary_dest));
				inet_ntop(AF_INET6, &binary_dest, \
						dest_addr, sizeof(dest_addr));
			}
			if (route_dest->rta_type == RTA_OIF)	{
				int * oif = (int *) RTA_DATA(route_dest);
				iface = odhcpd_get_interface_by_index(*oif);
			}
			if (route_dest->rta_type ==  RTA_PRIORITY && iface)	{
				int * metric = (int *) RTA_DATA(route_dest);
				if(*metric == 1024 && !strncmp(iface->name, "lan", 3))	{
					syslog(LOG_DEBUG, "ping_pan: send ping to %s", dest_addr);
					struct sockaddr_in6 dest = {AF_INET6, 0, 0, binary_dest, iface->ifindex};
					struct icmp6_hdr echo = {.icmp6_type = ICMP6_ECHO_REQUEST};
					struct iovec iov = {&echo, sizeof(echo)};

					odhcpd_send(pan_ping_socket, &dest, &iov, 1, iface);

					struct pan_node *node = NULL;
					bool found = false;
					char dest_addr1[INET6_ADDRSTRLEN];
					list_for_each_entry(node, &pan_nodes, head)	{
						inet_ntop(AF_INET6, &node->destAddr, \
									dest_addr1, sizeof(dest_addr1));
						if(!memcmp(&node->destAddr, &binary_dest, sizeof(binary_dest)))	{
							found = true;
							node->got_resp = false;
							break;
						}
					}
					if(!found)	{
						node = calloc(1, sizeof(*node));
						memcpy(&node->destAddr, &binary_dest, sizeof(binary_dest));
						node->ifindex = iface->ifindex;
						node->got_resp = false;
						list_add(&node->head, &pan_nodes);
					}
				}
			}
		}
	}

uloop_add:
	uloop_timeout_set(t,60000);

}


// Send an ICMP-ECHO. This is less for actually pinging but for the
// neighbor cache to be kept up-to-date.
static void ping6(struct in6_addr *addr,
		const struct interface *iface)
{

	struct sockaddr_in6 dest = {AF_INET6, 0, 0, *addr, iface->ifindex};
	struct icmp6_hdr echo = {.icmp6_type = ICMP6_ECHO_REQUEST};
	struct iovec iov = {&echo, sizeof(echo)};

	if (iface->support_slip && !strncmp(iface->name, "lan", 3))	{
		odhcpd_setup_route(addr, 128, iface, NULL, 128, true);
		odhcpd_send(pan_ping_socket, &dest, &iov, 1, iface);
		odhcpd_setup_route(addr, 128, iface, NULL, 128, false);
	}
	else	{
		odhcpd_setup_route(addr, 128, iface, NULL, 128, true);
		odhcpd_send(ping_socket, &dest, &iov, 1, iface);
		odhcpd_setup_route(addr, 128, iface, NULL, 128, false);
	}

}

static void handle_ping_resp(struct uloop_fd *u, _unused unsigned int events)
{
	char buf[512];
	char dest_addr[INET6_ADDRSTRLEN];
	struct sockaddr_in6 addr;
	socklen_t len;
	bool found = false;
	struct interface *iface = NULL;

	recvfrom(u->fd, buf, sizeof(buf), 0, (struct sockaddr*)&addr, &len);
	iface = odhcpd_get_interface_by_name("sl0");

	if (!iface)
		return;

	struct pan_node *node = NULL;
	list_for_each_entry(node, &pan_nodes, head)	{
		if(!memcmp(&node->destAddr, &addr.sin6_addr, sizeof(addr.sin6_addr)))	{
			node->got_resp = true;
			found = true;
			odhcpd_setup_route(&addr.sin6_addr, 128, iface, NULL, 1024, true);
			inet_ntop(AF_INET6, &addr.sin6_addr, \
						dest_addr, sizeof(dest_addr));

			syslog(LOG_DEBUG, "handle_ping_resp - Destination %s and node->got_resp %d", dest_addr, node->got_resp);
		}
	}

	if(found == false)	{
		odhcpd_setup_route(&addr.sin6_addr, 128, iface, NULL, 1024, true);
		inet_ntop(AF_INET6, &addr.sin6_addr, \
						dest_addr, sizeof(dest_addr));

		syslog(LOG_DEBUG, "Onetime: Added route to Destination %s ", dest_addr);
	}
}

// Handle solicitations
static void handle_solicit(void *addr, void *data, size_t len,
		struct interface *iface, _unused void *dest)
{
	struct ip6_hdr *ip6 = data;
	struct nd_neighbor_solicit *req = (struct nd_neighbor_solicit*)&ip6[1];
	struct sockaddr_ll *ll = addr;

	// Solicitation is for duplicate address detection
	bool ns_is_dad = IN6_IS_ADDR_UNSPECIFIED(&ip6->ip6_src);

	// Don't forward any non-DAD solicitation for external ifaces
	// TODO: check if we should even forward DADs for them
	if (iface->external && !ns_is_dad)
		return;

	if (len < sizeof(*ip6) + sizeof(*req))
		return; // Invalid reqicitation

	if (IN6_IS_ADDR_LINKLOCAL(&req->nd_ns_target) ||
			IN6_IS_ADDR_LOOPBACK(&req->nd_ns_target) ||
			IN6_IS_ADDR_MULTICAST(&req->nd_ns_target))
		return; // Invalid target

	char ipbuf[INET6_ADDRSTRLEN];
	inet_ntop(AF_INET6, &req->nd_ns_target, ipbuf, sizeof(ipbuf));
	syslog(LOG_DEBUG, "Got a NS for %s", ipbuf);

	uint8_t mac[6];
	odhcpd_get_mac(iface, mac);
	if (!memcmp(ll->sll_addr, mac, sizeof(mac)))
		return; // Looped back

	struct interface *c;
	list_for_each_entry(c, &interfaces, head)	{
		if (iface->ndp == RELAYD_RELAY && (strcmp(iface->ifname, c->ifname)) &&
				(strcmp(c->ifname, "lo")) &&
				(ns_is_dad || !c->external))
			ping6(&req->nd_ns_target, c);
	}
}

// Use rtnetlink to modify kernel routes
static void setup_route(struct in6_addr *addr, struct interface *iface, bool add)
{
	char namebuf[INET6_ADDRSTRLEN];
	inet_ntop(AF_INET6, addr, namebuf, sizeof(namebuf));
	syslog(LOG_NOTICE, "%s about %s on %s",
			(add) ? "Learned" : "Forgot", namebuf, iface->ifname);

	if (iface->learn_routes)
		odhcpd_setup_route(addr, 128, iface, NULL, 1024, add);
}

// compare prefixes
static int prefixcmp(const void *va, const void *vb)
{
	const struct odhcpd_ipaddr *a = va, *b = vb;
	uint32_t a_pref = ((a->addr.s6_addr[0] & 0xfe) != 0xfc) ? a->preferred : 1;
	uint32_t b_pref = ((b->addr.s6_addr[0] & 0xfe) != 0xfc) ? b->preferred : 1;
	return (a_pref < b_pref) ? 1 : (a_pref > b_pref) ? -1 : 0;
}

// Check address update
static void check_updates(struct interface *iface)
{
	struct odhcpd_ipaddr addr[8] = {{IN6ADDR_ANY_INIT, 0, 0, 0, 0}};
	time_t now = odhcpd_time();
	ssize_t len = odhcpd_get_interface_addresses(iface->ifindex, addr, 8);

	if (len < 0)
		return;

	qsort(addr, len, sizeof(*addr), prefixcmp);

	for (int i = 0; i < len; ++i) {
		addr[i].addr.s6_addr32[3] = 0;

		if (addr[i].preferred < UINT32_MAX - now)
			addr[i].preferred += now;

		if (addr[i].valid < UINT32_MAX - now)
			addr[i].valid += now;
	}

	bool change = len != (ssize_t)iface->ia_addr_len;
	for (ssize_t i = 0; !change && i < len; ++i)
		if (!IN6_ARE_ADDR_EQUAL(&addr[i].addr, &iface->ia_addr[i].addr) ||
				(addr[i].preferred > 0) != (iface->ia_addr[i].preferred > 0) ||
				addr[i].valid < iface->ia_addr[i].valid ||
				addr[i].preferred < iface->ia_addr[i].preferred)
			change = true;

	if (change)
		dhcpv6_ia_preupdate(iface);

	memcpy(iface->ia_addr, addr, len * sizeof(*addr));
	iface->ia_addr_len = len;

	if (change)
		dhcpv6_ia_postupdate(iface, now);

	if (change)
		raise(SIGUSR1);
}


// Handler for neighbor cache entries from the kernel. This is our source
// to learn and unlearn hosts on interfaces.
static void handle_rtnetlink(_unused void *addr, void *data, size_t len,
		_unused struct interface *iface, _unused void *dest)
{
	bool dump_neigh = false;
	struct in6_addr last_solicited = IN6ADDR_ANY_INIT;

	for (struct nlmsghdr *nh = data; NLMSG_OK(nh, len);
			nh = NLMSG_NEXT(nh, len)) {
		struct ndmsg *ndm = NLMSG_DATA(nh);
		struct rtmsg *rtm = NLMSG_DATA(nh);

		bool is_addr = (nh->nlmsg_type == RTM_NEWADDR
				|| nh->nlmsg_type == RTM_DELADDR);
		bool is_route = (nh->nlmsg_type == RTM_NEWROUTE
				|| nh->nlmsg_type == RTM_DELROUTE);
		bool is_neigh = (nh->nlmsg_type == RTM_NEWNEIGH
				|| nh->nlmsg_type == RTM_DELNEIGH);

		// Family and ifindex are on the same offset for NEIGH and ADDR
		if ((!is_addr && !is_route && !is_neigh)
				|| NLMSG_PAYLOAD(nh, 0) < sizeof(*ndm)
				|| ndm->ndm_family != AF_INET6)
			continue;

		// Inform about a change in default route
		if (is_route && rtm->rtm_dst_len == 0)
			raise(SIGUSR1);
		else if (is_route)
			continue;

		// Data to retrieve
		size_t rta_offset = (is_addr) ?	sizeof(struct ifaddrmsg) : sizeof(*ndm);
		uint16_t atype = (is_addr) ? IFA_ADDRESS : NDA_DST;
		ssize_t alen = NLMSG_PAYLOAD(nh, rta_offset);
		struct in6_addr *addr = NULL;

		for (struct rtattr *rta = (void*)(((uint8_t*)ndm) + rta_offset);
				RTA_OK(rta, alen); rta = RTA_NEXT(rta, alen)) {
			if (rta->rta_type == atype &&
					RTA_PAYLOAD(rta) >= sizeof(*addr)) {
				addr = RTA_DATA(rta);
			}
		}

		// Lookup interface
		struct interface *iface = odhcpd_get_interface_by_index(ndm->ndm_ifindex);
		if (!iface)
			continue;

		// Address not specified or unrelated
		if (!addr || IN6_IS_ADDR_LINKLOCAL(addr) ||
				IN6_IS_ADDR_MULTICAST(addr))
			continue;

		// Check for states
		bool add;
		if (is_addr)
			add = (nh->nlmsg_type == RTM_NEWADDR);
		else
			add = (nh->nlmsg_type == RTM_NEWNEIGH && (ndm->ndm_state &
				(NUD_REACHABLE | NUD_STALE | NUD_DELAY | NUD_PROBE
						| NUD_PERMANENT | NUD_NOARP)));

		if (iface->ndp == RELAYD_RELAY) {
			// Replay change to all neighbor cache
			struct {
				struct nlmsghdr nh;
				struct ndmsg ndm;
				struct nlattr nla_dst;
				struct in6_addr dst;
			} req = {
				{sizeof(req), RTM_DELNEIGH, NLM_F_REQUEST,
						++rtnl_seqid, 0},
				{.ndm_family = AF_INET6, .ndm_flags = NTF_PROXY},
				{sizeof(struct nlattr) + sizeof(struct in6_addr), NDA_DST},
				*addr
			};

			if (ndm->ndm_flags & NTF_PROXY) {
				// Dump & flush proxy entries
				if (nh->nlmsg_type == RTM_NEWNEIGH) {
					req.ndm.ndm_ifindex = iface->ifindex;
					send(rtnl_event.uloop.fd, &req, sizeof(req), MSG_DONTWAIT);
					setup_route(addr, iface, false);
					dump_neigh = true;
				}
			} else if (add) {
				struct interface *c;
				list_for_each_entry(c, &interfaces, head) {
					if (iface == c)
						continue;

					if (c->ndp == RELAYD_RELAY) {
						req.nh.nlmsg_type = RTM_NEWNEIGH;
						req.nh.nlmsg_flags |= NLM_F_CREATE | NLM_F_REPLACE;

						req.ndm.ndm_ifindex = c->ifindex;
						send(rtnl_event.uloop.fd, &req, sizeof(req), MSG_DONTWAIT);
					} else { // Delete NDP cache from interfaces without relay
						req.nh.nlmsg_type = RTM_DELNEIGH;
						req.nh.nlmsg_flags &= ~(NLM_F_CREATE | NLM_F_REPLACE);

						req.ndm.ndm_ifindex = c->ifindex;
						send(rtnl_event.uloop.fd, &req, sizeof(req), MSG_DONTWAIT);
					}
				}

				setup_route(addr, iface, true);
			} else {
				if (nh->nlmsg_type == RTM_NEWNEIGH) {
					// might be locally originating
					if (!IN6_ARE_ADDR_EQUAL(&last_solicited, addr)) {
						last_solicited = *addr;

						struct interface *c;
						list_for_each_entry(c, &interfaces, head)
							if (iface->ndp == RELAYD_RELAY && iface != c &&
									!c->external == false)
								ping6(addr, c);
					}
				} else {
					struct interface *c;
					list_for_each_entry(c, &interfaces, head) {
						if (c->ndp == RELAYD_RELAY && iface != c) {
							req.ndm.ndm_ifindex = c->ifindex;
							send(rtnl_event.uloop.fd, &req, sizeof(req), MSG_DONTWAIT);
						}
					}
					setup_route(addr, iface, false);

					// also: dump to add proxies back in case it moved elsewhere
					dump_neigh = true;
				}
			}
		}

		if (is_addr) {
			check_updates(iface);

			if (iface->dhcpv6 == RELAYD_SERVER)
				iface->ia_reconf = true;

			if (iface->ndp == RELAYD_RELAY && iface->master) {
				// Replay address changes on all slave interfaces
				nh->nlmsg_flags = NLM_F_REQUEST;

				if (nh->nlmsg_type == RTM_NEWADDR)
					nh->nlmsg_flags |= NLM_F_CREATE | NLM_F_REPLACE;

				struct interface *c;
				list_for_each_entry(c, &interfaces, head) {
					if (c->ndp == RELAYD_RELAY && !c->master) {
						ndm->ndm_ifindex = c->ifindex;
						send(rtnl_event.uloop.fd, nh, nh->nlmsg_len, MSG_DONTWAIT);
					}
				}
			}
		}
	}

	if (dump_neigh)
		dump_neigh_table(false);
}

static void catch_rtnetlink(int error)
{
	if (error == ENOBUFS) {
		struct {
			struct nlmsghdr nh;
			struct ifaddrmsg ifa;
		} req2 = {
			{sizeof(req2), RTM_GETADDR, NLM_F_REQUEST | NLM_F_DUMP,
					++rtnl_seqid, 0},
			{.ifa_family = AF_INET6}
		};
		send(rtnl_event.uloop.fd, &req2, sizeof(req2), MSG_DONTWAIT);
	}
}
