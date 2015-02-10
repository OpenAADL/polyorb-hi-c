/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#ifndef __PO_HI_DRIVER_PUS_EVENTS_H__
#define __PO_HI_DRIVER_PUS_EVENTS_H__

#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_NORMAL            1
#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_ERROR_LOW         1<<1
#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_ERROR_MEDIUM      (1<<1)|1
#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_ERROR_HIGH        1<<2
#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_REPORT_ENABLE     (1<<2|1<<1)
#define __PO_HI_DRIVER_PUS_EVENTS_SUBTYPE_REPORT_DISABLE    (1<<2|1)

/*
 * The following code needs extra declaration to work.
 *
 * Generated code must contain at least two definition :
 * 1. The __po_hi_driver_pus_rid_t type that is an
 *    enumeration and describe all Report Identifier
 *    we can have in the system.
 *    ex :
 *       typedef
 *       {
 *          pus_rid_sensor_value_too_high = 1,
 *          pus_rid_sensor_error          = 2
 *       }__po_hi_driver_pis_rid_t;
 *
 * 2. The __PO_HI_DRIVER_PUS_EVENTS_NB_EVENTS maccro
 *    that specifies the number of events we have in
 *    the whole architecture.
 *    ex : #define __PO_HI_DRIVER_PUS_EVENTS_NB_EVENTS 2
 */

int __po_hi_driver_pus_events_report (uint8_t                  severity, 
                                      __po_hi_driver_pus_rid_t rid,
                                      char*                    parameters,
                                      int                      param_len);
/*
 * This function is used to report events using TM packets.
 * This is describe in the section 10.3 of the ECSS-E-70-41A
 * standard (page 80). The severity argument specifies
 * if this is a normal or an error report (and details
 * its severity). The rid argument is the Report-Identifier,
 * it should be generated from system specifications and
 * correspond to an enumeration. Finally, the parameters
 * argument contains optional parameters of the report while
 * the param_len argument represent the length of these optional
 * parameters. In case of no parameter, param_len = 0.
 *
 * Returns __PO_HI_SUCCESS if the report is sent successfully,
 * other value otherwise. Please have a look at po_hi_returns
 * file for all return codes.
 */

int __po_hi_driver_pus_events_disable (char* data);
int __po_hi_driver_pus_events_enable (char* data);
/*
 * The following functions are used to enable/disable events report.
 * The argument is only a data, structured as in section 10.3.2
 * of the ECSS-E-70-41A standard. It can contain one or several
 * Report Identifier to enable/disable. This data should be structured
 * as follow :
 *
 *  _____________________________________
 * | NRID  |  RID1 | RID2 | .... | RID-N |
 *  -------------------------------------
 *
 *  If only one RID must be enable/disable, the content
 *  is only : 
 *
 *   _______________________
 *  | RID TO ENABLE/DISABLE |
 *   -----------------------
 *
 *
 * When enable a report generation, the subtype if 6 while
 * the subtype is 5 when you want to disable a report
 * event generation.
 *
 * Also, enable/disable a report generation is an additional
 * capability set and is not mandatory.
 *
 * These functions returns __PO_HI_SUCCESS is successfull, another
 * value otherwise.
 */


#endif /* __PO_HI_DRIVER_PUS_EVENTS_H__ */
