/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
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

#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_LIST_FULL      14
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_EXIST          15
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NO_ACCESS      16
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NOT_BOOLEAN    17

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
   __po_hi_int_t  check_position;
   int            check_selection_parameter;
}__po_hi_driver_pus_parameter_monitoring_modification_t;

typedef struct
{
   __po_hi_pus_parameter_monitoring_pid_t                      pid;
   __po_hi_uint32_t                                            interval;
   __po_hi_uint32_t                                            n_values;
   /* Number of values that are monitored before issuing a value check */
   __po_hi_uint32_t                                            n_delta;
   /* Number of values that are monitored before issuing a delta check */
   __po_hi_uint32_t                                            n_limit_checks;
   __po_hi_uint32_t                                            n_delta_checks;
   __po_hi_uint32_t                                            n_expected_checks;
   __po_hi_driver_pus_parameter_monitoring_limit_check_t       limit_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
   __po_hi_driver_pus_parameter_monitoring_delta_check_t       delta_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
   __po_hi_driver_pus_parameter_monitoring_expected_check_t    expected_checks[__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_MAX_CHECK_PER_ITEM];
}__po_hi_driver_pus_parameter_monitoring_item_t;



typedef struct
{
   __po_hi_bool_t                                              enable;
   __po_hi_uint32_t                                            max_reporting_delay;
   __po_hi_uint32_t                                            n_items;
   __po_hi_driver_pus_parameter_monitoring_item_t              items;
}__po_hi_driver_pus_parameter_monitoring_status_t;


#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_EXPECTED_VALUE       0
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_WITHIN_LIMITS        0
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_WITHIN_THRESOLDS     0
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_UNCHECKED            1
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_INVALID              2
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_UNSELECTED           3
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_UNEXPECTED_VALUE     4
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_BELOW_LIMIT          4
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_BELOW_THRESOLD       4
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_ABOVE_LIMIT          5
#define   __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_ABOVE_THRESOLD       5

typedef struct
{

   __po_hi_pus_parameter_monitoring_pid_t                      pid;
   char*                                                       param_value;
   char*                                                       limit_crossed;
   __po_hi_uint8_t                                             previous_status;
   /* 
    * Correspond to a value of the macro 
    * __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_* 
    */
   __po_hi_uint8_t                                             current_status;
   /* 
    * Correspond to a value of the macro 
    * __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_CHECKING_STATUS_* 
    */
   __po_hi_time_t                                              crossed_time;
}__po_hi_driver_pus_parameter_monitoring_report_status_item_t;


typedef struct
{
   __po_hi_uint32_t                                               n_items;
   __po_hi_driver_pus_parameter_monitoring_report_status_item_t*  items;
}__po_hi_driver_pus_parameter_monitoring_ool_status_t;


typedef struct
{
   __po_hi_uint32_t                                               n_items;
   __po_hi_driver_pus_parameter_monitoring_report_status_item_t*  items;
}__po_hi_driver_pus_parameter_monitoring_check_transition_report_t;


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
 * The interval parameter corresponds to the interval at which parameters are
 * monitored.
 * The n_samples_values param corresponds to the number of values should be
 * sampled before a value monitoring report.
 * The n_samples_delta param corresponds to the number of values that should be
 * sampled before issuing a delta monitoring report.
 * The n_parameters param indicates how many parameters are we adding to the
 * monitoring list.
 * The data param contains relevant data for adding one or several monitoring
 * report definition to the list.
 * The data_length param defines the size of the data parameter.
 *
 * The data parameter is structured as in the 15.3.4 section of the ECSS PUS
 * standard. It repeats n_parameters times the same sequence that defines the
 * addition of a parameter to the monitoring list.
 *
 * Returns : 
 *    __PO_HI_SUCCESS             if no error is encountered.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_LIST_FULL 
 *                               if the monitoring list is full
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_EXIST
 *                               if the parameter is already monitored.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NO_ACCESS
 *                               if the parameter is not accessible.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NOT_BOOLEAN
 *                               if the parameter is not boolean.
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
 * Returns 
 *    __PO_HI_SUCCESS if no error is encountered.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_LIST_FULL 
 *                               if the monitoring list is full
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_EXIST
 *                               if the parameter is already monitored.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NO_ACCESS
 *                               if the parameter is not accessible.
 *    __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_ERROR_NOT_BOOLEAN
 *                               if the parameter is not boolean.
 */

int __po_hi_driver_pus_parameter_monitoring_delete_item (__po_hi_driver_pus_pid_t pid);
/*
 * Delete a parameter from the monitoring list.
 * The pid param corresponds to the parameter to remove from the list.
 *
 * Returns 
 *    __PO_HI_SUCCESS if no error is encountered.
 */

int __po_hi_driver_pus_parameter_monitoring_delete_items (__po_hi_uint32_t n_parameters,
                                                          char*            data,
                                                          __po_hi_uint32_t data_length);
/*
 * Delete several parameters from the parameter list. The n_parameters param
 * indicates how many parameters are removed from the list. The data param is
 * a raw structure that contain all parameter id to be removed. The data_length
 * size specifies the size of the data param.
 *
 * Correspond to subtype 6
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_DELETE)
 * 
 * Returns 
 *    __PO_HI_SUCCESS if no error is encountered.
 */

int __po_hi_driver_pus_parameter_monitoring_modify_item (__po_hi_driver_pus_pid_t pid,
                                                         __po_hi_bool_t                                             is_valid,
                                                         __po_hi_uint32_t                                           n_limit_checks,
                                                         __po_hi_driver_pus_parameter_monitoring_modification_t*    checks_modifications;
                                                         __po_hi_driver_pus_parameter_monitoring_limit_check_t*     limit_checks,
                                                         __po_hi_uint32_t                                           n_delta_checks,
                                                         __po_hi_driver_pus_parameter_monitoring_modification_t*    delta_modifications;
                                                         __po_hi_driver_pus_parameter_monitoring_delta_check_t*     delta_checks,
                                                         __po_hi_uint32_t                                           n_expected_checks,
                                                         __po_hi_driver_pus_parameter_monitoring_modification_t*    expected_modifications;
                                                         __po_hi_driver_pus_parameter_monitoring_expected_check_t*  expected_checks);

/*
 * Modify the monitoring of one parameter. The checks_modifications,
 * delta_modifications and expected_modifications parameters correspond to the
 * "Check Position" and "Check Selection Parameter#" item in section 1.3.6 of
 * the standard. For each modified parameter, we must have a value in
 * *_modifications data that indicate how the change are applied.
 *
 * Returns __PO_HI_SUCCESS if no error is encountered.
 */



int __po_hi_driver_pus_parameter_monitoring_modify_items (__po_hi_uint32_t n_parameters,
                                                          char*            data,
                                                          __po_hi_uint32_t data_length);
/*
 * Modify several parameters from the parameter list. The n_parameters param
 * indicates how many parameters are removed from the list. The data param is
 * a structure, detailed in section 15.3.6 of the standard.
 *
 * Correspond to service subtype 7 of the service 12.
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_MODIFY)
 * 
 * Returns 
 *    __PO_HI_SUCCESS if no error is encountered.
 */

int __po_hi_driver_pus_parameter_monitoring_report_list ();
/*
 * Report the list of ALL monitored parameters. Correspond to service subtype 8
 * (ask for report, TC packet - __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_REPORT_ASK)
 * and 9 (send the report, TM packet - __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_LIST_REPORT_ANSWER).
 *
 * Returns __PO_HI_SUCCESS if no error are encountered.
 */


int __po_hi_driver_pus_parameter_monitoring_report_ool ();
/*
 * Issue a report with ALL out of limit parameters. This corresponds to the
 * service subtype 10 (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_OOL_ASK)
 * for the TC packet and service 11 (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_OOL_ANSWER)
 * for the TM packet.
 *
 * Correspond to the section 15.3.8 of the ECSS standard.
 *
 * Returns __PO_HI_SUCCESS if no error are encountered.
 */


int __po_hi_driver_pus_parameter_monitoring_report_check_transitions ();
/*
 * Report the transition list that have been performed since the last report.
 * Correspond to service subtype 12
 * (__PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_CHECK_TRANSITION_REPORT)
 * and it sends a TM packet to the ground that contains the check transitions
 * informations. The packet structure is detailed in section 15.3.9 of the ECSS
 * standard.
 *
 * Returns __PO_HI_SUCCESS if no error are encountered.
 */



#endif /* __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_H__ */
