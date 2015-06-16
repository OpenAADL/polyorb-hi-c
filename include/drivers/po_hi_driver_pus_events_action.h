/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#ifndef __PO_HI_DRIVER_PUS_EVENTS_ACTION_H__
#define __PO_HI_DRIVER_PUS_EVENTS_ACTION_H__

/*
 * This file defines the functions that implement the Event-Action service
 * of the PUS protocol. This is denoted as service 19 in the PUS standard 
 * (ECSS-E-70-41A document).
 */

/*
 * This service requires the declaration of the following types and maccros:
 *  1. __po_hi_driver_pus_apid_t : definition of the APID type. This is most of
 *       the time an enumeration that enumerates each application id of the
 *       OBSW.
 *  2. __po_hi_driver_pus_rid_t : as for the apid_t type, we need a type
 *     that describes the events handled by the system. 
 *  3. __po_hi_driver_pus_action_t : as for the apid_t type and rid_t type,
 *     this enumerated all potential actions the system can perform.
 *  4. __PO_HI_DRIVER_PUS_NB_DETECTIONS : macro that indicates the size of
 *    the  detection list associated with this service. Using this configuration
 *    directive, we can statically allocate the actions detection list.
 */

#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_EVENTS_ADD           1                 /* Part of the minimum capability set */
#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_ACTIONS_ENABLE       1<<2              /* Part of the minimum capability set */
#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_ACTIONS_DISABLE      ((1<<2)|1)        /* Part of the minimum capability set */

#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_EVENTS_DELETE        (1<<1)            /* Part of the additional capability set */
#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_EVENTS_CLEAR         ((1<<1)|1)        /* Part of the additional capability set */
#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_EVENTS_REPORT_ASK    ((1<<1)|(1<<2))   /* Part of the additional capability set */
#define __PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_EVENTS_REPORT_SEND   ((1<<2)|(1<<1)|1) /* Part of the additional capability set */

typedef struct
{
   __po_hi_driver_pus_apid_t        apid;
   __po_hi_driver_pus_rid_t         rid;
   __po_hi_driver_pus_action_t      action;
   __po_hi_driver_action_status_t   action_status;
}__po_hi_driver_pus_detection_t;
/*
 * Content of an event detection and its corresponding action.
 */

typedef struct
{
   __po_hi_driver_pus_apid_t     apid;
   __po_hi_driver_pus_rid_t      rid;
   __po_hi_bool_t                enabled;
}__po_hi_driver_pus_events_action_report_t;
/*
 * A status report entry used for reporting the event detection list.
 * (see section 21.3.5 of the ECSS-70-E-41A for more details).
 */

int __po_hi_driver_pus_events_action_add_events_to_detection_list (char* content,
                                                                   int content_length);
/*
 * Add events to the detection list. The argument is only a buffer.
 * This buffer is only a RAW buffer that may contain several events to
 * add in the detection list. In that case, the structure of the buffer
 * is the following (as detailed in ECSS-E-70-41A) :
 *    ______________________________________
 *   |  N   | APID |   RID   |   TC PACKET  |
 *    --------------------------------------
 *          <------------------------------->
 *                  Repeated N times
 *
 *  If only one event is added, the content of the buffer is like this :
 *    _______________________________
 *   | APID |   RID   |   TC PACKET  |
 *    -------------------------------
 *
 *  For more information, refer to section 21.3.1 of the ECSS-E-70-41A
 *  standard.
 *
 *  This function returns __PO_HI_SUCCESS in case of success.
 */
 

int __po_hi_driver_pus_events_action_add_event_to_detection_list (__po_hi_driver_pus_apid_t apid,
                                                                  __po_hi_driver_pus_rid_t  rid,
                                                                  char*                     action,
                                                                  int                       action_length);
/*
 * Add an event/action to the detection list. The apid argument is the
 * application id that is generating the report. The rid is the identifier
 * of the event that is reported. The action argument contains the definition
 * of the action while the action_length argument specifies the size of the 
 * action.
 *
 * Returns __PO_HI_SUCCESS if successfull.
 */
 

int __po_hi_driver_pus_events_action_delete_events_from_detection_list (char* content,
                                                                        int content_length);
/*
 * Delete one or several event/action from the detection list. The argument is a
 * buffer which structure is like this (as detailed in ECSS-E-70-41A) :
 *    _______________________
 *   |  N   | APID |   RID   | 
 *    -----------------------
 *          <--------------->
 *          Repeated N times
 *
 *  If only one event is deleted, the content of the buffer is like this :
 *    ________________
 *   | APID |   RID   |
 *    ----------------
 *
 *  For more information, refer to section 21.3.2 of the ECSS-E-70-41A
 *  standard.

 * *
 * Returns __PO_HI_SUCCESS if successfull.
 */

int __po_hi_driver_pus_events_action_delete_event_from_detection_list (__po_hi_driver_pus_apid_t apid,
                                                                       __po_hi_driver_pus_rid_t  rid);
/*
 * Delete an event/action from the detection list. The apid argument is the
 * application id that is generating the report. The rid is the identifier
 * of the event that is reported.
 *
 * Returns __PO_HI_SUCCESS if successfull.
 */

int __po_hi_driver_pus_events_action_clear_detection_list ();
/*
 * Clear all entries from the detection list.
 *
 * Returns __PO_HI_SUCCESS is no error is reported.
 */

int __po_hi_driver_pus_events_action_events_enable (char* data,
                                                    int data_length);
/*
 * Enable one or several events. The data argument is a raw package and
 * the data_length argument is the length of the data.
 *
 * It corresponds to subservice 4
 * (__PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_ACTIONS_ENABLE)
 *
 * The data argument structure is like this :
 *    _____________________
 *   |  N  | APID  |  RID  |
 *    ---------------------
 *          <------------->
 *          Repeated N times
 * See page 178 of the ECSS standard to have a full description, section 21.3.4.
 * The N value correspond to the number of events to enable.
 * So, for each event, the data contain the APID and the Event
 * Identifier that will be enable to trigger an action.
 *
 * Returns __PO_HI_SUCCESS if no error are raised.
 */

int __po_hi_driver_pus_events_action_events_disable (char* data,
                                                     int data_length);
/*
 * Disable one or several events. The data argument is a raw package and
 * the data_length argument is the length of the data.
 *
 * It corresponds to subservice 5
 * (__PO_HI_DRIVER_PUS_EVENT_ACTION_SUBTYPE_ACTIONS_DISABLE)
 *
 * The data argument structure is like this :
 *    _____________________
 *   |  N  | APID  |  RID  |
 *    ---------------------
 *          <------------->
 *          Repeated N times
 * See page 178 of the ECSS standard to have a full description, section 21.3.4.
 * The N value correspond to the number of events to disable.
 * So, for each event, the data contain the APID and the Event
 * Identifier for which the triggered action will be disabled.
 *
 * Returns __PO_HI_SUCCESS if no error are raised.
 */


int __po_hi_driver_pus_events_action_event_enable (__po_hi_driver_pus_apid_t apid,
                                                   __po_hi_driver_pus_rid_t  rid);
/*
 * Enable an action for a specific event generated by a specific application id.
 * The apid argument is the one that generates the event and the rid argument
 * is the identifier of the generated event.
 *
 * Returns __PO_HI_SUCCESS is there is no error.
 */


int __po_hi_driver_pus_events_action_event_disable (__po_hi_driver_pus_apid_t apid,
                                                    __po_hi_driver_pus_rid_t  rid);
/*
 * Disable an action for a specific event generated by a specific application id.
 * The apid argument is the one that generates the event and the rid argument
 * is the identifier of the generated event.
 *
 * Returns __PO_HI_SUCCESS is there is no error.
 */



int __po_hi_driver_pus_events_action_event_report ();
/*
 * Send the report detection list. It consists of a packet that contain
 * all events/action registered in the detection list. To generate
 * this report, we use the __po_hi_driver_pus_events_action_report_t type.
 */


#endif /* __PO_HI_DRIVER_PUS_EVENTS_ACTION_H__ */
