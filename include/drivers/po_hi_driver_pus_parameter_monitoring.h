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

#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_ENABLE                   1
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_DISABLE                  1<<1
#define __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_SUBTYPE_CHANGE_REPORTING_DELAY   ((1<<1)|1)

/*
 * This file is part of the implementation of the Parameter
 * Monitoring service of PUS (service type 12).
 */

/*
 * To work, this code must be interfaces with code generated
 * from Ocarina/TASTE. It requires the following definitions:
 *  - BLABLA
 */

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


#endif /* __PO_HI_DRIVER_PUS_PARAMETER_MONITORING_H__ */
