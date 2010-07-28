/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency.
 */

#ifndef __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_H__ 
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_H__ 

/*
 * This file is part of the implementation of the Parameter
 * Monitoring service of PUS (service type 12).
 */

/*
 * To work, this code must be interfaces with code generated
 * from Ocarina/TASTE. It requires the following definitions:
 *  - __po_hi_driver_pus_rid_t : event identifiers
 *  - __po_hi_driver_pus_pid_t : parameter identifiers
 *  - __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_LIST_SIZE : size of the monitoring
 *    list.
 */


#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM 4


#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_ENABLE                   1                   /* 01 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_DISABLE                  1<<1                /* 02 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_CHECK_TRANSITION_REPORT  ((1<<3)|(1<<2))     /* 12 */
/*
 * The following are the minimum capabilities
 */


#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_CHANGE_REPORTING_DELAY   ((1<<1)|1)          /* 03 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_CLEAR               ((1<<2))            /* 04 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_ADD                 ((1<<2)|1)          /* 05 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_DELETE              ((1<<2)|(1<<1))     /* 06 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_MODIFY              ((1<<2)|(1<<1)|1)   /* 07 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_REPORT_ASK          (1<<3)              /* 08 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_REPORT_ANSWER       ((1<<3)|1)          /* 09 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_OOL_ASK                  ((1<<3)|(1<<1))     /* 10 */
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_OOL_ANSWER               ((1<<3)|(1<<1)|1)   /* 11 */
/*
 * The following are additional capabilities.
 */

typedef struct
{
   char*                      low_limit;
   __po_hi_driver_pus_rid_t   low_limit_rid,
   char*                      high_limit;
   __po_hi_driver_pus_rid_t   high_limit_rid,
}__po_hi_driver_pus_parameter_monitoring_limit_check_t;


typedef struct
{
   char*                      low_delta;
   __po_hi_driver_pus_rid_t   low_delta_rid,
   char*                      high_delta;
   __po_hi_driver_pus_rid_t   high_delta_rid,
}__po_hi_driver_pus_parameter_monitoring_delta_check_t;


typedef struct
{
   char*                      expected_value;
   __po_hi_driver_pus_rid_t   rid,
}__po_hi_driver_pus_parameter_monitoring_expected_check_t;

typedef struct
{
   __po_hi_uint32_t                                            interval;
   __po_hi_uint32_t                                            n_values;
   /* Number of values that are monitored before issuing a value check */
   __po_hi_uint32_t                                            n_delta;
   /* Number of values that are monitored before issuing a delta check */
   __po_hi_pus_parameter_monitoring_pid_t                      pid;
   __po_hi_uint32_t                                            n_limit_checks;
   __po_hi_uint32_t                                            n_delta_checks;
   __po_hi_uint32_t                                            n_expected_checks;
   __po_hi
   __po_hi_driver_pus_parameter_monitoring_limit_check_t       limit_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
   __po_hi_driver_pus_parameter_monitoring_delta_check_t       delta_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
   __po_hi_driver_pus_parameter_monitoring_expected_check_t    expected_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
}__po_hi_driver_pus_parameter_monitoring_item_t;


int __po_hi_driver_pus_parameter_monitoring_enable (char* data, int data_length);
/*
 * Enable the monitoring of one, several or all parameters.
 * The data argument is RAW data while the data_length arg specifies the size
 * of the data argument.
 * It corresponds to subtype 1 
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_ENABLE).
 *
 * The data argument is structured like this :
 *      ___________________________________________
 *     |  N  | PARAM 1 | PARAM 2 | ..... | PARAM N |
 *      -------------------------------------------
 *            <------->
 *         Repeated N times
 *
 * The value of N indicates the number of parameter to enable.
 * If N = 0, then, the whole monitoring of all parameters
 * is enable.
 *
 * Returns __PO_HI_SUCCESS if no error is raised.
 */

int __po_hi_driver_pus_parameter_monitoring_disable (char* data, int data_length);
/*
 * Disable the monitoring of one, several or all parameters.
 * The data argument is RAW data while the data_length arg specifies the size
 * of the data argument.
 * It corresponds to subtype 2
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_DISABLE).
 *
 * The data argument is structured like this :
 *      ___________________________________________
 *     |  N  | PARAM 1 | PARAM 2 | ..... | PARAM N |
 *      -------------------------------------------
 *            <------->
 *         Repeated N times
 *
 * The value of N indicates the number of parameter to disable.
 * If N = 0, then, the whole monitoring of all parameters
 * is disable.
 *
 * Returns __PO_HI_SUCCESS if no error is raised.
 */


int __po_hi_driver_pus_parameter_monitoring_change_reporting_delay (__po_hi_uint32_t delay);
/*
 * Change the reporting delay. Correspond to section 15.3.2 of the ECSS
 * standard, subtype 3 (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_CHANGE_REPORTING_DELAY).
 *
 * Returns __PO_HI_SUCCESS if no error is detected.
 */


int __po_hi_driver_pus_parameter_monitoring_clear ();
/*
 * Clear the monitoring list. Correspond to service subtype 4
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_CLEAR)
 *
 * Returns __PO_HI_SUCCESS if no error is encountered.
 */


int __po_hi_driver_pus_parameter_monitoring_add_items (__po_hi_uint32_t                                          interval,
                                                      __po_hi_uint32_t                                           n_samples_values,
                                                      __po_hi_uint32_t                                           n_samples_delta,
                                                      __po_hi_uint32_t                                           n_parameters,
                                                      char*                                                      data,
                                                      __po_hi_uint32_t                                           data_length);
/*
 * Returns __PO_HI_SUCCESS if no error is encountered.
 */


int __po_hi_driver_pus_parameter_monitoring_add_item (__po_hi_uint32_t                                           interval,
                                                      __po_hi_uint32_t                                           n_samples_values,
                                                      __po_hi_uint32_t                                           n_samples_delta,
                                                      __po_hi_driver_pus_pid_t                                   pid,
                                                      __po_hi_bool_t                                             is_valid,
                                                      __po_hi_uint32_t                                           n_limit_checks,
                                                      __po_hi_driver_pus_parameter_monitoring_limit_check_t*     limit_checks,
                                                      __po_hi_uint32_t                                           n_delta_checks,
                                                      __po_hi_driver_pus_parameter_monitoring_delta_check_t*     delta_checks,
                                                      __po_hi_uint32_t                                           n_expected_checks,
                                                      __po_hi_driver_pus_parameter_monitoring_expected_check_t*  expected_checks);

/*
 * Returns __PO_HI_SUCCESS if no error is encountered.
 */


#endif /* __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_H__ */
