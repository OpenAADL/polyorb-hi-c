/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_RTEMS_NE2000_SOCKETS

#include <bsp.h>
#include <rtems/rtems_bsdnet.h>

#include <po_hi_transport.h>
#include <po_hi_debug.h>

#include <drivers/po_hi_driver_sockets.h>

extern __po_hi_device_id socket_device_id;

extern struct rtems_bsdnet_ifconfig netdriver_config;
char __po_hi_rtems_ethernet_address[6] = { 0x52, 0x54, 0x00, 0x12, 0x34, 0x57}; 

extern __po_hi_inetnode_t nodes[__PO_HI_NB_DEVICES];
extern __po_hi_inetnode_t rnodes[__PO_HI_NB_DEVICES];

void __po_hi_driver_rtems_ne2000_init (__po_hi_device_id id)
{
   char* dev_conf;
   char dev_addr[16];
   int  dev_port;
   int node;

   memset (dev_addr, '\0', 16);

   for (node = 0 ; node < __PO_HI_NB_DEVICES ; node++)
   {
      nodes[node].socket = -1;
   }


   dev_conf = __po_hi_get_device_naming (id);
   dev_port = 0;

   if (sscanf (dev_conf, "ip %s %d", dev_addr, &dev_port) == 0)
   {
      __DEBUGMSG ("[DRIVER SOCKETS] Unable to parse device configuration (id=%d)\n", id);
   }

   __DEBUGMSG ("My configuration, addr=%s, port=%d\n", dev_addr, dev_port);

   memset (netdriver_config.ip_address, '\0', 15);
   memcpy (netdriver_config.ip_address, dev_addr, strlen (dev_addr));
   memcpy (netdriver_config.ip_netmask, "255.255.255.0", 13);

   __DEBUGMSG ("Set configuration addr for RTEMS=%s\n", netdriver_config.ip_address);

   __po_hi_rtems_ethernet_address[5] = (dev_port + 23) % 254;

   netdriver_config.hardware_address = __po_hi_rtems_ethernet_address;

   __DEBUGMSG ("Init RTEMS\n");

   if (rtems_bsdnet_initialize_network () != RTEMS_SUCCESSFUL)
   {
      __DEBUGMSG ("Error when initializing RTEMS network\n");
      return;
   }
   __DEBUGMSG ("RTEMS network init done\n");

#ifdef __PO_HI_DEBUG
   rtems_bsdnet_show_if_stats ();
#endif

   __po_hi_driver_sockets_common_generic_init (id, __po_hi_sockets_poller);
}

#endif
