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

#pragma once
#include "odhcpd.h"
#include <time.h>

#ifndef SOL_NETLINK
#define SOL_NETLINK 270
#endif

#define NDP_MAX_NEIGHBORS 1000

struct ndp_neighbor {
	struct list_head head;
	struct interface *iface;
	struct in6_addr addr;
	uint8_t len;
	time_t timeout;
};

struct pan_node  {
	struct list_head head;
	struct in6_addr destAddr;
	int ifindex;
	bool got_resp;
};
