#ifndef __REQUEST_H_
#define __REQUEST_H_ 
#include <types.h>
#include <deployment.h>
/*  Enumeration type for all the operations in the distributed application.*/

typedef struct
{
   __po_hi_port_t port;

   union
   {
      struct
      {
         simple_type ping_me_global_data_sink;

      } ping_me_global_data_sink;

      struct
      {
         simple_type pinger_global_data_source;

      } pinger_global_data_source;

   } vars;

} __po_hi_request_t;

#define __PO_HI_NB_OPERATIONS 0

#endif
