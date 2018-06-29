/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

/**
 * This header file defines data types and functions to support the
 * AADL Code Generation Annex (Annex C) published in document
 * AS5506/1A.
 *
 */

#include <deployment.h>

/**
 * Definition of AADL thread context (AS5506/1A C.6.3)
 *
 * Note: in PolyORB-HI/C, all port variables are part of the internal
 * structure defined in po_hi_gqueue.h. The thread context is
 * therefore limited to the identifier of a task.
 */

typedef __po_hi_task_id  __aadl_context;

/**
 * Helper macros to access AADL entities
 *
 * A typical use case is
 *
 * 1) Definition of AADL request type
 * __po_hi_request_t request;
 *
 * 2) Definition of the output port to use
 * request.port = REQUEST_PORT (a_thread, a_port);
 *
 * 3) Assignment to the corresponding port variable
 * request.PORT_VARIABLE (a_thread, a_port) = a_value;
 *
 *  4) We send the request through the thread *local* port, built from
 *     the instance name and the port name using the LOCAL_PORT
 *     macro. PolyORB-HI/C middleware will later propagate the request to
 *     its destination
 *
 * __po_hi_gqueue_store_out
 *   (self,
 *    LOCAL_PORT (waterlevelmonitoring_thread, wateralarm),
 *    &request);
 *
 */

#define LOCAL_PORT(THREAD_INSTANCE_NAME, PORT_NAME) THREAD_INSTANCE_NAME ## _local_ ## PORT_NAME

/**
 * REQUEST_PORT macro builds a handle to the output port used when
 * building a request
 */
#define REQUEST_PORT(THREAD_INSTANCE_NAME, PORT_NAME) THREAD_INSTANCE_NAME ## _global_ ## PORT_NAME

/**
 * PORT_VARIABLE macro build a handle to a port variable
 */
#define PORT_VARIABLE(THREAD_INSTANCE_NAME, PORT_NAME) vars.REQUEST_PORT(THREAD_INSTANCE_NAME,PORT_NAME).REQUEST_PORT(THREAD_INSTANCE_NAME,PORT_NAME)


/**
 * Put_Value (AS5506C): A Put_Value runtime service allows the source
 * text of a thread to supply a data value to a port variable. This
 * data value will be transmitted at the next Send_Output call in the
 * source text or by the runtime system at completion time or
 * deadline.
 *
 * subprogram Put_Value features
 *   Portvariable: requires data access; -- reference to port variable
 *   DataValue: in parameter;            -- value to be stored
 *   DataSize: in parameter;             -- size in bytes (optional)
 * end Put_Value;
 *
 */
