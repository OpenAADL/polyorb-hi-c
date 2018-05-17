/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2007-2009 Telecom ParisTech, 2010-2014 ESA & ISAE.
 */

#include <po_hi_config.h>

#ifdef __PO_HI_USE_GIOP

/*
 * This is the GIOP implementation for PolyORB-HI-C. It tries to be compliant
 * with the GIOP standard.
 * You can see how are structured the message at the following address :
 * http://publib.boulder.ibm.com/infocenter/javasdk/v1r4m2/index.jsp?topic=/com.ibm.java.doc.diagnostics.142j9/html/corbagiop.html
 */

#include <po_hi_giop.h>
#include <po_hi_types.h>
#include <po_hi_messages.h>
#include <po_hi_transport.h>
#include <po_hi_returns.h>
#include <po_hi_debug.h>

#include <deployment.h>
#include <request.h>

#ifdef __PO_HI_DEBUG
#include <stdio.h>
#endif

uint16_t __po_hi_request_id = 0;

extern const char* __po_hi_ports_names[__PO_HI_NB_PORTS];

void __po_hi_giop_msg_hdr_init (__po_hi_giop_msg_hdr_t* msg_hdr)
{
  msg_hdr->magic[0]       = 'G';
  msg_hdr->magic[1]       = 'I';
  msg_hdr->magic[2]       = 'O';
  msg_hdr->magic[3]       = 'P';
  msg_hdr->version.major  = __PO_HI_GIOP_VERSION_MAJOR;
  msg_hdr->version.minor  = __PO_HI_GIOP_VERSION_MINOR;
  
#ifdef WORDS_BIGENDIAN
  msg_hdr->flags          = 0; /* Should set 1 if we use big endian representation    */
#else                                /* clause. In a near future, should deal with autoconf */
  msg_hdr->flags          = 1; /* to know if the target is big or little endian       */
#endif
  
  msg_hdr->message_type   = __PO_HI_GIOP_MSGTYPE_REQUEST;
  msg_hdr->message_size   = 0; /* the user must specify the size with the        */
  /* function __po_hi_giop_msg_hdr_set_message_size */
}

void __po_hi_giop_request_hdr_init (__po_hi_giop_request_hdr_t* request_hdr)
{
  request_hdr->request_id                                   = ++__po_hi_request_id;
  request_hdr->response_flags                               = 0; /* oneway ? */
  request_hdr->reserved[0]                                  = 0;
  request_hdr->reserved[1]                                  = 0;
  request_hdr->reserved[2]                                  = 0;
  request_hdr->target.disposition                           = __PO_HI_GIOP_DISPOSITION_KEY;
  request_hdr->target.values.key.object_size                = 0;
  request_hdr->target.values.key.object_addr                = 0;
  request_hdr->nb_scontext                                  = 0;
}

void __po_hi_giop_msg_hdr_set_message_type (__po_hi_giop_msg_hdr_t* msg_hdr,
                                            __po_hi_uint8_t msg_type)
{
  msg_hdr->message_type = msg_type;
}


void __po_hi_giop_msg_hdr_set_message_size (__po_hi_giop_msg_hdr_t* msg_hdr,
                                            __po_hi_uint32_t msg_size)
{
  msg_hdr->message_size = msg_size;
}

void __po_hi_giop_request_hdr_set_operation (__po_hi_giop_request_hdr_t* request_hdr,
                                             const char* request_name)
{
  int len;
  len = strlen (request_name);
  strncpy( request_hdr->operation, request_name, len);
  request_hdr->operation[len] = '\0';
  request_hdr->operation_length = len;
}

int __po_hi_giop_send (__po_hi_entity_t from,
                       __po_hi_entity_t to,
                       __po_hi_msg_t* msg)
{
  /* msg holds
   *   [0 .. sizeof (__po_hi_port_t) - 1] -> id of the port
   *
   *   [sizeof (__po_hi_port_t) .. msg-> len] -> request payload
   *   encoded as CDR data
   */

  __po_hi_uint16_t           port_name_length;
  __po_hi_uint32_t           giop_message_size;
  __po_hi_msg_t              smsg;
  __po_hi_giop_msg_hdr_t     msg_hdr;
  __po_hi_giop_request_hdr_t request_hdr;
  __po_hi_port_t             port_id;
  const char*                port_name;
  
  __po_hi_msg_get_data (&port_id, msg, 0, sizeof (__po_hi_port_t));
  
  port_name        = __po_hi_ports_names[port_id];
  port_name_length = strlen (port_name);
#ifdef __PO_HI_DEBUG
  __DEBUGMSG ("port name %s\n", port_name);
  __DEBUGMSG ("msg length %d\n", msg->length);
#endif

  /*
   * Per CORBA 3.1, Part 2, Section 9.4,
   *
   * giop_message_size        = GIOP request_header + CDR content
   *
   * GIOP request_header size = fixed size of the header (23) +
   *      operation_length
   *
   * CDR content size         = sizeof (msg) - sizeof (__po_hi_port_t)
   * fixed size of the header =
   *  24 (Request Header for GIOP 1.2, for AddressingDisposition = KeyAddr
   *  XXX check size of service_context, for now it is 4
   */

  giop_message_size = 26 + port_name_length + 1 
    + msg->length - sizeof (__po_hi_port_t);
  
  __po_hi_msg_reallocate (&smsg);
  
  __po_hi_giop_msg_hdr_init (&msg_hdr);
  __po_hi_giop_msg_hdr_set_message_size (&msg_hdr, giop_message_size);

  __po_hi_giop_request_hdr_init (&request_hdr);  
  __po_hi_giop_request_hdr_set_operation (&request_hdr, port_name);
  
  __po_hi_msg_append_data (&smsg, msg_hdr.magic, __PO_HI_GIOP_MAGIC_SIZE);
  __po_hi_msg_append_data (&smsg, &(msg_hdr.version.major), 1);
  __po_hi_msg_append_data (&smsg, &(msg_hdr.version.minor), 1);
  __po_hi_msg_append_data (&smsg, &(msg_hdr.flags) , 1);
  __po_hi_msg_append_data (&smsg, &(msg_hdr.message_type) , 1);
  __po_hi_msg_append_data (&smsg, &(msg_hdr.message_size) , 4);
  
  __po_hi_msg_append_data (&smsg, &(request_hdr.request_id) , sizeof (__po_hi_uint32_t));
  __po_hi_msg_append_data (&smsg, &(request_hdr.response_flags) , 1);
  __po_hi_msg_append_data (&smsg, &(request_hdr.reserved[0]) , 1);
  __po_hi_msg_append_data (&smsg, &(request_hdr.reserved[1]) , 1);
  __po_hi_msg_append_data (&smsg, &(request_hdr.reserved[2]) , 1);
  __po_hi_msg_append_data (&smsg, &(request_hdr.target.disposition) , 2);
  __po_hi_msg_append_data (&smsg, &(request_hdr.target.values.key.object_size) , 4);
  __po_hi_msg_append_data (&smsg, &(request_hdr.target.values.key.object_addr) , 4);
  __po_hi_msg_append_data (&smsg, &(request_hdr.operation_length) , 4);
  __po_hi_msg_append_data (&smsg, request_hdr.operation, request_hdr.operation_length + 1);
  __po_hi_msg_append_data (&smsg, &(request_hdr.nb_scontext) , sizeof(__po_hi_uint32_t));
  __po_hi_msg_append_data (&smsg, &msg->content[sizeof(__po_hi_port_t)] , msg->length - sizeof(__po_hi_port_t));

#ifdef __PO_HI_DEBUG
  __po_hi_giop_print_msg(&smsg);
#endif

  return __po_hi_sockets_send (from, to, &smsg);
}


int __po_hi_giop_decode_msg (__po_hi_msg_t* network_flow, __po_hi_msg_t* output_msg, __po_hi_uint32_t* has_more)
{
  static __po_hi_giop_msg_hdr_t     msg_hdr;
  __po_hi_giop_request_hdr_t request_hdr;
  __po_hi_port_t             port_identifier;
  __po_hi_uint8_t            port_found;

  if (*has_more == 0)
    {
      msg_hdr.magic[0]       = network_flow->content[0];
      msg_hdr.magic[1]       = network_flow->content[1];
      msg_hdr.magic[2]       = network_flow->content[2];
      msg_hdr.magic[3]       = network_flow->content[3];
      msg_hdr.version.major  = network_flow->content[4];
      msg_hdr.version.minor  = network_flow->content[5];
      msg_hdr.flags          = network_flow->content[6];
      msg_hdr.message_type   = network_flow->content[7];
      __po_hi_msg_get_data (&msg_hdr.message_size, network_flow, 8, sizeof (__po_hi_uint32_t));
      
      if (msg_hdr.flags == 0)
	{
	  output_msg->flags = __PO_HI_MESSAGES_CONTENT_BIGENDIAN;
	}
      else
	{
	  output_msg->flags = __PO_HI_MESSAGES_CONTENT_LITTLEENDIAN;
	}

      if ((msg_hdr.version.major !=  __PO_HI_GIOP_VERSION_MAJOR) &&
	  (msg_hdr.version.minor !=  __PO_HI_GIOP_VERSION_MINOR))
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("Invalid version, we only support GIOP v%d.%d, got %d %d\n",
		      __PO_HI_GIOP_VERSION_MAJOR,
		      __PO_HI_GIOP_VERSION_MINOR,
		      msg_hdr.version.major,
		      msg_hdr.version.minor);
#endif
	  return (__PO_HI_GIOP_INVALID_VERSION);
	}
      
      if (msg_hdr.message_type != __PO_HI_GIOP_MSGTYPE_REQUEST)
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("Bad message type, we only support request message");
#endif
	  return (__PO_HI_GIOP_INVALID_REQUEST_TYPE);
	}


      *has_more =  msg_hdr.message_size;
      return (__PO_HI_SUCCESS);
    }
  else
    {
      *has_more = 0;
                  
      __po_hi_msg_get_data (&request_hdr.request_id, 
			    network_flow, 
			    12 - sizeof (__po_hi_giop_msg_hdr_t), 
			    sizeof (__po_hi_uint32_t));
      request_hdr.response_flags   = network_flow->content[16 - sizeof (__po_hi_giop_msg_hdr_t)];
      request_hdr.reserved[0]      = network_flow->content[17 - sizeof (__po_hi_giop_msg_hdr_t)];
      request_hdr.reserved[1]      = network_flow->content[18 - sizeof (__po_hi_giop_msg_hdr_t)];
      request_hdr.reserved[2]      = network_flow->content[19 - sizeof (__po_hi_giop_msg_hdr_t)];
      __po_hi_msg_get_data (&request_hdr.target.disposition, 
			    network_flow, 
			    20  - sizeof(__po_hi_giop_msg_hdr_t), 
			    2);
      
      if (request_hdr.target.disposition != __PO_HI_GIOP_DISPOSITION_KEY)
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("This target disposition is not supported by this GIOP implementation");
#endif
	  return (__PO_HI_GIOP_UNSUPPORTED);
	}
      
      /*
       * We check that the disposition invoked is the only supported by
       * our implementation of GIOP
       */
      
      __po_hi_msg_get_data (&request_hdr.target.values.key.object_size, network_flow, 22 - sizeof(__po_hi_giop_msg_hdr_t), 4);
      __po_hi_msg_get_data (&request_hdr.target.values.key.object_addr, network_flow, 26 - sizeof(__po_hi_giop_msg_hdr_t), 4);
      
      __po_hi_msg_get_data (&request_hdr.operation_length, network_flow, 30  - sizeof(__po_hi_giop_msg_hdr_t), 4);
      
      if (request_hdr.operation_length >= __PO_HI_GIOP_OPERATION_MAX_SIZE)
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("The requested operation is not known by this server");
#endif
	  return (__PO_HI_GIOP_INVALID_OPERATION);
	}
      
      __po_hi_msg_get_data (&request_hdr.operation, 
			    network_flow, 
			    34  - sizeof(__po_hi_giop_msg_hdr_t), 
			    request_hdr.operation_length + 1);
      /* We get the operation. The size if operation_length + 1 byte set to 0 */
      
      __po_hi_msg_get_data (&request_hdr.nb_scontext, 
			    network_flow, 
			    34 + request_hdr.operation_length + 1  - sizeof(__po_hi_giop_msg_hdr_t), 
			    sizeof(__po_hi_uint32_t));
      
      if (request_hdr.nb_scontext != 0)
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("This implementation of GIOP does not support contextes");
#endif
	  return (__PO_HI_GIOP_UNSUPPORTED);
	}
      /*
       * This implementation of GIOP does not support contexts. For
       * that, we return the unsupported return-code.
       */
      port_found = 0;
      for (port_identifier=0 ; port_identifier < __PO_HI_NB_PORTS ; port_identifier++)
	{
	  if (strcmp(__po_hi_ports_names[port_identifier],request_hdr.operation) == 0)
	    {
	      port_found = 1;
	      break;
	    }
	}
      
      if (! port_found)
	{
#ifdef __PO_HI_DEBUG
	  __DEBUGMSG ("Invalid operation %s\n", request_hdr.operation);
#endif
	  
	  return (__PO_HI_GIOP_INVALID_OPERATION);
	}
      
      __po_hi_msg_write (output_msg, &port_identifier, sizeof (__po_hi_port_t));
#ifdef __PO_HI_DEBUG
      __DEBUGMSG ("Payload size: %d\n", msg_hdr.message_size - request_hdr.operation_length - 26 - 1 );
#endif
      __po_hi_msg_append_data (output_msg, 
			       &network_flow->content[38 + request_hdr.operation_length + 1  - sizeof(__po_hi_giop_msg_hdr_t)], 
			       msg_hdr.message_size - request_hdr.operation_length - 27 );
#ifdef __PO_HI_DEBUG
      __po_hi_messages_debug (output_msg);
#endif 
      
      return (__PO_HI_SUCCESS);
    }
}

#ifdef __PO_HI_DEBUG

void __po_hi_giop_print_msg( __po_hi_msg_t* msg)
{
        __po_hi_uint32_t len;
        __po_hi_uint32_t oplen;
        __po_hi_uint32_t ncontext;

	__po_hi_messages_debug (msg);

        printf("-----------------------------\n");
        printf("-- GIOP Header               \n");
        printf("-----------------------------\n");
        printf("Magic 1        = %c\n",msg->content[0]);
        printf("Magic 2        = %c\n",msg->content[1]);
        printf("Magic 3        = %c\n",msg->content[2]);
        printf("Magic 4        = %c\n",msg->content[3]);
        printf("Major          = %d\n",msg->content[4]);
        printf("Minor          = %d\n",msg->content[5]);
        printf("Flags          = %d\n",msg->content[6]);
        printf("Message Type   = %d\n",msg->content[7]);
        printf("Message Size   = %d\n",msg->content[8]);
        printf("----------------------------\n");
        printf("-- GIOP Request Header      \n");
        printf("----------------------------\n");
        printf("Request-id     = %d\n",msg->content[12]);
        printf("Response flags = %d\n",msg->content[16]);
        printf("Reserved 1     = %d\n",msg->content[17]);
        printf("Reserved 1     = %d\n",msg->content[18]);
        printf("Reserved 1     = %d\n",msg->content[19]);
        printf("Target dispo   = %u\n",msg->content[20]);
        printf("Object key len = %u\n",msg->content[22]);
        printf("Object key adr = %u\n",msg->content[26]);
        __po_hi_msg_get_data (&oplen, msg, 30 , sizeof(__po_hi_uint32_t));
        printf("Op length      = %u\n",oplen);
        printf("Op name        = ");
        for (len = 0 ; len < oplen ; len++)
        {
	  printf("%c", msg->content[34 + len]);
        }
        printf("\n");
        __po_hi_msg_get_data (&ncontext, msg, 34 + oplen , sizeof(__po_hi_uint32_t));
        printf("Nb contextes   = %u\n",ncontext);
        printf("----------------------------\n");
        printf("-- GIOP Body                \n");
        printf("----------------------------\n");
        printf("0x");
        for (len=38 + oplen ; len < msg->length ; len++ )
        {
                printf("%x", msg->content[len]);
        }
        printf("\n");


        printf ("Total length =%d\n", msg->length);
}
#endif /* __PO_HI_DEBUG */

#endif /* __PO_HI_USE_GIOP */
