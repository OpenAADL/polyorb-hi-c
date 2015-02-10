/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2008-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#include <rtems.h>
#include <rtems/rtems_bsdnet.h>

extern void rtems_bsdnet_loopattach();
static struct rtems_bsdnet_ifconfig loopback_config = {
        "lo0",                          /* name */
        (int (*)(struct rtems_bsdnet_ifconfig *, int))rtems_bsdnet_loopattach, /* at
                                                                                  tach function */
        NULL,                           /* link to next interface */
        "127.0.0.1",                    /* IP address */
        "255.0.0.0",                    /* IP net mask */
};

struct rtems_bsdnet_config rtems_bsdnet_config = {
        &loopback_config,       /* Network interface */
        NULL,                   /* Use fixed network configuration */
        0,                      /* Default network task priority */
        0,                      /* Default mbuf capacity */
        0,                      /* Default mbuf cluster capacity */
        "testSystem",           /* Host name */
        "nowhere.com",          /* Domain name */
        "127.0.0.1",            /* Gateway */
        "127.0.0.1",            /* Log host */
        {"127.0.0.1" },         /* Name server(s) */
        {"127.0.0.1" },         /* NTP server(s) */
};
