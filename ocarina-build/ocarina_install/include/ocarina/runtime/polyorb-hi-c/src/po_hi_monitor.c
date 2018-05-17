/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2017 ESA & ISAE.
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

#include <stddef.h> /* Definition of the NULL macro */

#include <deployment.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_monitor.h>
#include <po_hi_returns.h>

#if __PO_HI_MONITOR_ENABLED == 1

__po_hi_monitor_failure_t __po_hi_monitor_failures_devices[__PO_HI_NB_DEVICES][__PO_HI_MONITOR_NB_FAILURES];
__po_hi_monitor_failure_t __po_hi_monitor_failures_buses[__PO_HI_NB_BUSES][__PO_HI_MONITOR_NB_FAILURES];

int __po_hi_monitor_n_failures_devices[__PO_HI_NB_DEVICES];
int __po_hi_monitor_n_failures_buses[__PO_HI_NB_BUSES];


void __po_hi_monitor_init (void)
{
   int i;

   /*
    * Initialise the monitoring subsystem, we assume that everything is
    * working when initializing the system.
    */
   for (i = 0 ; i < __PO_HI_NB_DEVICES ; i++)
   {
      __po_hi_monitor_n_failures_devices[i] = 0;
   }

   for (i = 0 ; i < __PO_HI_NB_BUSES ; i++)
   {
      __po_hi_monitor_n_failures_buses[i] = 0;
   }
   __PO_HI_DEBUG_DEBUG ("[MONITOR] Initialized the monitoring subsystem\n");
}


int __po_hi_monitor_get_status_port (const __po_hi_port_t port, __po_hi_monitor_status_t* status)
{
   __po_hi_device_id associated_device;
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_port with argument %d (port) and 0x%p (status pointer)\n", port, status);

   associated_device = __po_hi_get_device_from_port (port);
   if (associated_device == invalid_device_id)
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] This port is not associated to a valid device (device-id=%d)\n", associated_device);
      return __PO_HI_UNAVAILABLE;
   }
   return __po_hi_monitor_get_status_device (associated_device, status);
}

int __po_hi_monitor_get_status_device (const __po_hi_device_id device,
                                       __po_hi_monitor_status_t* status)
{
   int               n_failure;
   uint32_t          n_buses;
   __po_hi_bus_id*   buses;
   uint32_t i;

   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_device with argument %d (device) and 0x%p (status pointer)\n", device, status);

   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }

   n_failure = __po_hi_monitor_n_failures_devices[device];

   n_buses = __po_hi_transport_get_n_accessed_buses (device);
   buses   = __po_hi_transport_get_accessed_buses (device);
   for (i = 0 ; i < n_buses ; i++)
   {
      if (__po_hi_monitor_get_status_bus (buses[i], status) == __PO_HI_SUCCESS)
      {
         if (status->status != po_hi_monitor_status_ok)
         {

            __PO_HI_DEBUG_DEBUG ("[MONITOR] return status of failed bus %d\n", i);
            return __PO_HI_SUCCESS;
         }
      }
   }

   if (n_failure == 0)
   {
      status->status = po_hi_monitor_status_ok;
      status->n_failures = 0;
      status->failures = NULL;
   }
   else
   {
      status->status = po_hi_monitor_status_ko;
      status->n_failures = n_failure;
      status->failures = __po_hi_monitor_failures_devices[device];
   }

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_get_status_bus (const __po_hi_bus_id       bus,
                                    __po_hi_monitor_status_t*  status)
{
   int               n_failure;

   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_get_status_bus with argument %d (bus) and 0x%p (status pointer)\n", bus, status);

   if ((bus < 0) || (bus >= __PO_HI_NB_BUSES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid bus-id %d\n", bus);
      return __PO_HI_UNAVAILABLE;
   }

   n_failure = __po_hi_monitor_n_failures_buses[bus];

   if (n_failure == 0)
   {
      status->status = po_hi_monitor_status_ok;
      status->n_failures = 0;
      status->failures = NULL;
   }
   else
   {
      status->status = po_hi_monitor_status_ko;
      status->n_failures = n_failure;
      status->failures = __po_hi_monitor_failures_buses[bus];
   }

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_bus (const __po_hi_bus_id bus,
                                        const __po_hi_monitor_failure_t failure)
{
   int n_failure;

   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_bus with argument %d (bus) and %d (failure)\n", bus, failure);


   if ((bus < 0) || (bus >= __PO_HI_NB_BUSES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid bus-id %d\n", bus);
      return __PO_HI_UNAVAILABLE;
   }

   n_failure = __po_hi_monitor_n_failures_buses[bus];
   if (n_failure >= __PO_HI_MONITOR_NB_FAILURES)
   {
      return __PO_HI_TOOMANY;
   }

   __po_hi_monitor_n_failures_buses[bus] = n_failure + 1;

   __po_hi_monitor_failures_buses[bus][n_failure] = failure;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_device (const __po_hi_device_id device,
                                           const __po_hi_monitor_failure_t failure)
{
   int n_failure;

   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_device with argument %d (device) and %d (failure)\n", device, failure);

   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }

   n_failure = __po_hi_monitor_n_failures_devices[device];
   if (n_failure >= __PO_HI_MONITOR_NB_FAILURES)
   {

      return __PO_HI_TOOMANY;
   }

   __po_hi_monitor_n_failures_devices[device] = n_failure + 1;

   __po_hi_monitor_failures_devices[device][n_failure] = failure;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_report_failure_port (const __po_hi_port_t port,
                                         const __po_hi_monitor_failure_t failure)
{
   __po_hi_device_id associated_device;
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_report_failure_port with argument %d (port) and %d (failure)\n", port, failure);

   associated_device = __po_hi_get_device_from_port (port);
   if (associated_device == invalid_device_id)
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] This port is not associated to a valid device (device-id=%d)\n", associated_device);
      return __PO_HI_UNAVAILABLE;
   }
   return __po_hi_monitor_report_failure_device (associated_device, failure);
}

int __po_hi_monitor_recover_bus (const __po_hi_bus_id bus)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_bus with argument %d\n", bus);
   if ((bus < 0) || (bus >= __PO_HI_NB_BUSES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid bus-id %d\n", bus);
      return __PO_HI_UNAVAILABLE;
   }

   __po_hi_monitor_n_failures_buses[bus] = 0;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_recover_device (const __po_hi_device_id device)
{
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_device with argument %d\n", device);
   if ((device < 0) || (device >= __PO_HI_NB_DEVICES))
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] invalid device-id %d\n", device);
      return __PO_HI_UNAVAILABLE;
   }

   __po_hi_monitor_n_failures_devices[device] = 0;

   return __PO_HI_SUCCESS;
}

int __po_hi_monitor_recover_port (const __po_hi_port_t port)
{
   __po_hi_device_id associated_device;
   __PO_HI_DEBUG_DEBUG ("[MONITOR] call __po_hi_monitor_recover_port with argument %d\n", port);

   associated_device = __po_hi_get_device_from_port (port);
   if (associated_device == invalid_device_id)
   {
      __PO_HI_DEBUG_CRITICAL ("[MONITOR] This port is not associated to a valid device (device-id=%d)\n", associated_device);
      return __PO_HI_UNAVAILABLE;
   }
   return __po_hi_monitor_recover_device (associated_device);
}

#endif
