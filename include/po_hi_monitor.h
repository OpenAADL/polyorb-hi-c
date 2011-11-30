#ifndef __PO_HI_MONITOR_H__
#define __PO_HI_MONITOR_H__

#include <deployment.h>
#include <po_hi_returns.h>

typedef enum
{
   po_hi_monitor_status_ok             = 0,        /* Working */
   po_hi_monitor_status_ko,            = 1,        /* Not working for unknown reason */
   po_hi_monitor_status_unavailable    = 2         /* No longer available, it used to work previously */
}__po_hi_monitor_status_t;

typedef enum
{
   po_hi_monitor_failure_unknown       = 0,        /* Unknown failure: something failed but we don't know what */
   po_hi_monitor_failure_value         = 1,        /* Bad value was sent or received */
}__po_hi_monitor_failure_t;


/*
 * __po_hi_monitor_get_status_port reports the status of the bus 
 * connected to the port given in parameter. Store the status in the second
 * parameter.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the port requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_UNKNOWN    - unknown resource. Typically because the
 *                                 second argument is invalid (e.g. NULL
 *                                 pointer).
 */
int __po_hi_monitor_get_status_port (__po_hi_port_t port, __po_hi_monitor_status_t* );

/*
 * __po_hi_monitor_get_status_device reports the status of the bus 
 * connected to the device given in parameter. Store the status in the second
 * parameter. The first argument corresponds to the device identifier
 * available in the deployment.h. The value can be either a numeric one or 
 * infered from the AADL model.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the device requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_UNKNOWN    - unknown resource. Typically because the
 *                                 second argument is invalid (e.g. NULL
 *                                 pointer).
 */
int __po_hi_monitor_get_status_device (__po_hi_device_id, __po_hi_monitor_status_t* );

/*
 * __po_hi_monitor_get_status_bus reports the status of the bus 
 * given in parameter. Store the status in the second
 * parameter. The value can be either a numeric one or 
 * infered from the AADL model. This information is available
 * in the deployment.h generated file.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the bus requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_UNKNOWN    - unknown resource. Typically because the
 *                                 second argument is invalid (e.g. NULL
 *                                 pointer).
 */
int __po_hi_monitor_get_status_bus (__po_hi_bus_id, __po_hi_monitor_status_t* );

/*
 * __po_hi_nonitor_report_failure reports a failure on the device/bus
 * associated to the port provided as parameter. First parameter
 * is the port bounded to the device/bus, the second argument is the kind
 * of failure to report. Depending on the failure value, the device/bus
 * is put to an invalid mode/state.
 *
 * If the failure to pass as argument is not known or does not exist,
 * users can use the po_hi_monitor_failure_unknown value.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the port requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_INVALID    - the value of the second argument is
 *                                 invalid.
 */
int __po_hi_monitor_report_failure (__po_hi_port_t, __po_hi_monitor_failure_t);

#endif

