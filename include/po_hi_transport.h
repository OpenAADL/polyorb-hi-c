/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2007-2008, GET-Telecom Paris.
 * Copyright (C) 2010, European Space Agency.
 */

#ifndef __PO_HI_TRANSPORT__
#define __PO_HI_TRANSPORT__

#include <po_hi_messages.h>
#include <deployment.h>
#include <request.h>

#define __PO_HI_BIGENDIAN     0
#define __PO_HI_LITTLEENDIAN  1

typedef struct
{
      void (*marshaller)   (void*, void*);
      void (*unmarshaller) (void*, void*);
}__po_hi_protocol_conf_t;

#if __PO_HI_NB_PORTS > 0

typedef uint8_t __po_hi_queue_id;

__po_hi_node_t    __po_hi_transport_get_node_from_entity (const __po_hi_entity_t entity);
/*
 * Returns the node identifier that corresponds to an entity.
 */

__po_hi_entity_t  __po_hi_get_entity_from_global_port (const __po_hi_port_t port);
/*
 * Return the entity identifier that own the port in parameters.
 */

/*
 * \fn            __po_hi_transport_send_default
 * \brief         Default transport layer function.
 */
int               __po_hi_transport_send_default (__po_hi_task_id id, __po_hi_port_t port);


/*
 * \fn      __po_hi_get_port_name
 * \brief   Return the name of the port similar to the name within the AADL model.
 */
char* __po_hi_get_port_model_name (const __po_hi_port_t port);

/*
 * \fn      __po_hi_get_port_name
 * \brief   Return the name of the port according to mapping rules.
 */
char* __po_hi_get_port_name (const __po_hi_port_t port);

/*
 * \fn      __po_hi_get_local_port_from_local_port
 * \brief   Return the local port identifier of the given global port to handle data on the node.
 */

__po_hi_local_port_t __po_hi_get_local_port_from_global_port (const __po_hi_port_t global_port);

/*
 * \fn      __po_hi_get_endianness
 * \brief   Return the endianness of the node given in parameter.
 *
 * The resulting value is either __PO_HI_BIGENDIAN  or __PO_HI_LITTLEENDIAN.
 */
__po_hi_uint8_t  __po_hi_get_endianness (const __po_hi_node_t node);

/*
 * \fn      __po_hi_get_device_from_port
 * \brief   Return the device associated with a given port.
 *
 * The resulting value is a device identifier generated in deployment.h.
 * If no device is associated with the port, it returns the constant
 * value invalid_device_id.
 */
__po_hi_device_id __po_hi_get_device_from_port (const __po_hi_port_t port);

char* __po_hi_get_device_naming (const __po_hi_device_id dev);

/*
 * \fn      __po_hi_get_device_configuration
 * \brief   Returns a pointer to the configuration data of the device.
 *
 * The configuration data can be either a string of a more complex
 * data structure, such as an instance of an ASN1 type.
 */
__po_hi_uint32_t* __po_hi_get_device_configuration (const __po_hi_device_id);


/*
 * \fn      __po_hi_transport_get_data_size
 * \brief   Returns the size of the data stored in the port given as parameter.
 */
__po_hi_uint32_t __po_hi_transport_get_data_size (const __po_hi_port_t portno);


/*
 * \fn      __po_hi_transport_get_queue_size
 * \brief   Return the size of the queue associated with the port.
 *
 * The size if specified as the number of request the port can store,
 * this is NOT the number of bytes that can be stored.
 */
__po_hi_uint32_t __po_hi_transport_get_queue_size (const __po_hi_port_t portno);

/*
 * \fn      __po_hi_transport_get_port_kind
 * \brief   Indicate the kind of the port given in parameter or __PO_HI_INVALID_PORT_KIND when not appropriate.
 *
 * The values that are returned indicate if the port is a pure event
 * port, if it has a data associated and if it is an inter-process
 * port or not.
 *
 * Potential return values are:
 *
 *  __PO_HI_IN_DATA_INTER_PROCESS
 *  __PO_HI_OUT_DATA_INTER_PROCESS
 *  __PO_HI_IN_DATA_INTRA_PROCESS
 *  __PO_HI_OUT_DATA_INTRA_PROCESS
 *  __PO_HI_IN_EVENT_DATA_INTER_PROCESS
 *  __PO_HI_OUT_EVENT_DATA_INTER_PROCESS
 *  __PO_HI_IN_EVENT_DATA_INTRA_PROCESS
 *  __PO_HI_OUT_EVENT_DATA_INTRA_PROCESS
 *  __PO_HI_IN_EVENT_INTER_PROCESS
 *  __PO_HI_OUT_EVENT_INTER_PROCESS
 *  __PO_HI_IN_EVENT_INTRA_PROCESS
 *  __PO_HI_OUT_EVENT_INTRA_PROCESS
 *  __PO_HI_INVALID_PORT_KIND
 */
__po_hi_port_kind_t __po_hi_transport_get_port_kind (const __po_hi_port_t portno);


/*
 * \fn      __po_hi_transport_get_model_name
 * \brief   Return the name of the port given in parameter.
 */

char*             __po_hi_transport_get_model_name (const __po_hi_port_t portno);


/* \fn      __po_hi_transport_get_mynode
 * \brief   Return the node identifier of the node that executes the current system.
 */
__po_hi_node_t    __po_hi_transport_get_mynode (void);


/*
 * \fn      __po_hi_transport_get_protocol
 * \brief   Return the protocol identifier that is used between port src and port dst.
 *
 * Get the protocol identifier used to communicate
 * between port src and port dst. It returns a protocol
 * identifier generated in deployment.h.
 * If no specific protocol is used, it returns the value
 * invalid_protocol.
 */
__po_hi_protocol_t         __po_hi_transport_get_protocol (const __po_hi_port_t src, const __po_hi_port_t dst);



/*
 * \fn      __po_hi_transport_get_protocol_configuration
 * \brief   Retrieve the configuration of the given protocol identifier. Returns a pointer on the conf or NULL.
 *      
 *
 * Protocol identifier can be retrieve in the generated deployment.h file
 * under the type __po_hi_protocol_t. Invalid protocol identifier
 * will result in returning NULL.
 */
__po_hi_protocol_conf_t*   __po_hi_transport_get_protocol_configuration (const __po_hi_protocol_t p);


#ifdef XM3_RTEMS_MODE
void __po_hi_transport_xtratum_port_init (const __po_hi_port_t portno, int val);
int __po_hi_transport_xtratum_get_port (const __po_hi_port_t portno);
#endif

#endif /* __PO_HI_NB_PORTS > 0 */



#endif /* __PO_HI_TRANSPORT__ */
