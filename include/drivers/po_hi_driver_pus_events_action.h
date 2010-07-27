/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2010, European Space Agency
 */

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
