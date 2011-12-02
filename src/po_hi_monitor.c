/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2011, European Space Agency.
 */

/*
 * \file po_hi_monitor.c
 *
 * \brief Contain the implementation of the monitoring service.
 *
 * For a description of the types being used, you can see
 * the file po_hi_monitor.h or also the deployment.h file
 * generated from AADL models.
 */

#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_monitor.h>
#include <po_hi_returns.h>

#if __PO_HI_MONITOR_ENABLED == 1

#ifndef __PO_HI_MONITOR_NB_FAILURES
#define __PO_HI_MONITOR_NB_FAILURES 10
#endif

__po_hi_monitor_status_t __po_hi_monitor_status_devices[__PO_HI_NB_DEVICES];
__po_hi_monitor_status_t __po_hi_monitor_status_buses[__PO_HI_NB_BUSES];


void __po_hi_monitor_init (void)
{
   int i;
   __PO_HI_DEBUG_DEBUG ("[MONITOR] Initialise the monitoring subsystem\n");

   /*
    * Initialise the monitoring subsystem, we assume that everything is
    * working when initializing the system.
    */
   for (i = 0 ; i < __PO_HI_NB_DEVICES ; i++)
   {
      __po_hi_monitor_status_devices[i] = po_hi_monitor_status_ok;
   }

   for (i = 0 ; i < __PO_HI_NB_BUSES ; i++)
   {
      __po_hi_monitor_status_buses[i] = po_hi_monitor_status_ok;
   }
}


int __po_hi_monitor_get_status_port (const __po_hi_port_t port, __po_hi_monitor_status_t* status)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_port with argument %d (port) and 0x%x (status pointer)\n", port, status);
   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_get_status_device (const __po_hi_device_id device,
                                       __po_hi_monitor_status_t* status)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_device with argument %d (device) and 0x%x (status pointer)\n", device, status);

   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_DEBUG ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }
   
   *status = __po_hi_monitor_status_devices[device];

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_get_status_bus (const __po_hi_bus_id bus,
                                    __po_hi_monitor_status_t* status)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_bus with argument %d (bus) and 0x%x (status pointer)\n", bus, status);
   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_bus (const __po_hi_bus_id bus, 
                                        const __po_hi_monitor_failure_t failure)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_bus with argument %d (bus) and %d (failure)\n", bus, failure);
   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_device (const __po_hi_device_id device,
                                           const __po_hi_monitor_failure_t failure)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_device with argument %d (device) and %d (failure)\n", device, failure);

   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_DEBUG ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }
   
   __po_hi_monitor_status_devices[device] = po_hi_monitor_status_ko;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_port (const __po_hi_port_t port,
                                         const __po_hi_monitor_failure_t failure)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_port with argument %d (port) and %d (failure)\n", port, failure);
   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_recover_bus (const __po_hi_bus_id bus)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_bus with argument %d\n", bus);
   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_recover_device (const __po_hi_device_id device)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_device with argument %d\n", device);
   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_DEBUG ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }
   
   __po_hi_monitor_status_devices[device] = po_hi_monitor_status_ok;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_recover_port (const __po_hi_port_t port)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_port with argument %d\n", port);
   return __PO_HI_SUCCESS;
}

#endif

