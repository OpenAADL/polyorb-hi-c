/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2014 ESA & ISAE.
 */

/*
 * \file po_hi_monitor.h
 *
 * \brief Contain the monitoring service functions.
 *
 * This file contains monitoring function to be used by either
 * PolyORB-HI-C services or application-level code. It is
 * useful to report errors related to a device or bus
 * or recovery of this entities.
 *
 * This service was introduced while tailoring/adapting PolyORB-HI-C
 * to SOIS standard. See http://cwe.ccsds.org/sois/default.aspx
 * So, most of the service features reflects SOIS requirements.
 */

#ifndef __PO_HI_MONITOR_H__
#define __PO_HI_MONITOR_H__

#include <deployment.h>
#include <po_hi_returns.h>

#ifndef __PO_HI_NB_BUSES
#define __PO_HI_NB_BUSES 0
#endif

#ifndef __PO_HI_MONITOR_NB_FAILURES
#define __PO_HI_MONITOR_NB_FAILURES 10
#endif

#ifndef __PO_HI_NB_DEVICES
#define __PO_HI_NB_DEVICES 0
#endif

#undef __PO_HI_MONITOR_ENABLED

#if ( (__PO_HI_NB_DEVICES > 0) || (__PO_HI_NB_BUSES > 0))
   #define __PO_HI_MONITOR_ENABLED 1
#endif

/*
 * \enum __po_hi_monitor_status_code_t
 *
 * \brief Status code for a bus/device. Indicated wether the 
 * entity is ok or not.
 */
typedef enum
{
   po_hi_monitor_status_ok             = 0,        /* Working */
   po_hi_monitor_status_ko             = 1,        /* Not working for unknown reason */
   po_hi_monitor_status_unavailable    = 2         /* No longer available, it used to work previously */
} __po_hi_monitor_status_code_t;


/*
 * \enum __po_hi_monitor_failure_t
 *
 * \brief Failure description that is used when reporting
 * a failure of a bus/device.
 */

typedef enum
{
   po_hi_monitor_failure_unknown       = 0,        /* Unknown failure: something failed but we don't know what */
   po_hi_monitor_failure_value         = 1         /* Bad value was sent or received */
} __po_hi_monitor_failure_t;

/*
 * \struct __po_hi_monitor_status_t
 *
 * \brief Structure that contains the status of an entity
 */

typedef struct
{
   __po_hi_monitor_status_code_t         status;
   int                           n_failures;
   __po_hi_monitor_failure_t*             failures;
} __po_hi_monitor_status_t;


/*
 * \fn __po_hi_monitor_init
 *
 * \brief Initialise the monitoring subsystem.
 *
 * This function is called by the main initialisation function of 
 * PolyORB-HI-C, __po_hi_initialize_early in __po_hi_main.c file
 */
void __po_hi_monitor_init (void);

#ifdef __PO_HI_MONITOR_ENABLED

/*
 * \fn __po_hi_monitor_get_status_port 
 *
 * \brief reports the status of the bus connected to the port given in parameter and store it in the second parameter.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the port requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_UNKNOWN    - unknown resource. Typically because the
 *                                 second argument is invalid (e.g. NULL
 *                                 pointer).
 */
int __po_hi_monitor_get_status_port (const __po_hi_port_t port, __po_hi_monitor_status_t*);

/*
 * \fn __po_hi_monitor_get_status_device 
 *
 * \brief reports the status of the bus connected to the device given in parameter in the second parameter.
 *
 * Store the status in the second
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
int __po_hi_monitor_get_status_device (const __po_hi_device_id, __po_hi_monitor_status_t* );

/*
 * \fn __po_hi_monitor_get_status_bus 
 *
 * \brief reports the status of the bus given in parameter in the second parameter.
 *
 * Store the status in the second
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
int __po_hi_monitor_get_status_bus (const __po_hi_bus_id, __po_hi_monitor_status_t* );

/*
 * \fn __po_hi_nonitor_report_failure_port
 *
 * \brief report a failure on the device/bus associated to the port provided as parameter.
 *
 * First parameter is the port bounded to the device/bus, the second argument is the kind
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
 *    - __PO_HI_TOOMANY          - The max number of failures that can be
 *                                 registered was already reached.
 */
int __po_hi_monitor_report_failure_port (const __po_hi_port_t, const __po_hi_monitor_failure_t);

/*
 * \fn __po_hi_nonitor_report_failure_device 
 *
 * \brief reports a failure (second parameter) against a device (first parameter).
 *
 * The device is indicated as first parameter. The second argument is the kind
 * of failure to report. Depending on the failure value, the device/bus
 * is put to an invalid mode/state.
 *
 * Note that the value of the first argument can be found/deduced
 * from the __po_hi_device_id type definition generated in deployment.h
 * file.
 *
 * If the failure to pass as argument is not known or does not exist,
 * users can use the po_hi_monitor_failure_unknown value.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the device requested is not available or does
 *                                 not exist.
 *    - __PO_HI_ERROR_INVALID    - the value of the second argument is
 *                                 invalid.
 *    - __PO_HI_TOOMANY          - The max number of failures that can be
 *                                 registered was already reached.
 */
int __po_hi_monitor_report_failure_device (const __po_hi_device_id, const __po_hi_monitor_failure_t);

/*
 * \fn __po_hi_nonitor_report_failure_bus 
 *
 * \brief Indicate that the bus pointed as first argument fails according to the failure pointed as second argument.
 *
 * This function reports a failure on the bus indicated
 * as first argument. The second argument is the kind
 * of failure to report. Depending on the failure value, the device/bus
 * is put to an invalid mode/state.
 *
 * If the failure to pass as argument is not known or does not exist,
 * users can use the po_hi_monitor_failure_unknown value.
 *
 * Note that the value of the first argument can be found/deduced
 * from the __po_hi_bus_id type definition generated in deployment.h
 * file.
 *
 * Returns the following codes:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the bus requested is not available or does
 *                                 not exist (invalid first argument).
 *    - __PO_HI_ERROR_INVALID    - the value of the second argument is
 *                                 invalid.
 *    - __PO_HI_TOOMANY          - The max number of failures that can be
 *                                 registered was already reached.
 */
int __po_hi_monitor_report_failure_bus (const __po_hi_bus_id, const __po_hi_monitor_failure_t);


/*
 * \fn __po_hi_monitor_recover_bus
 *
 * \brief Indicate that the bus pointed as parameter is fully functional
 *
 * Returns the following values:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the bus (argument to be used) is invalid.
 */
int __po_hi_monitor_recover_bus (const __po_hi_bus_id);

/*
 * \fn __po_hi_monitor_recover_device
 *
 * \brief Indicate that the device pointed as parameter is fully functional
 *
 * Returns the following values:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the device (argument to be used) is invalid.
 */
int __po_hi_monitor_recover_device (const __po_hi_device_id);


/*
 * \fn __po_hi_monitor_recover_port
 *
 * \brief Indicate that the bus/device bound to the point pointed as parameter is fully functional
 *
 * Returns the following values:
 *    - __PO_HI_SUCCESS          - if the operation was successful.
 *    - __PO_HI_UNAVAILABLE      - the port (argument to be used) is invalid.
 *
 * if the function returns __PO_HI_UNAVAILABLE, this is because either
 * the bus bound to the port or its device are not valid. Also,
 * if the port is not bound to any device/bus (local port, used for
 * communication on the local node only), it will also report an error.
 */
int __po_hi_monitor_recover_port (const __po_hi_port_t);

#endif

#endif
