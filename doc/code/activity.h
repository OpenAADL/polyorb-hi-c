#ifndef __ACTIVITY_H_
#define __ACTIVITY_H_ 
#include <request.h>
#include <po_hi_messages.h>
#include <deployment.h>
void pinger_deliver 
      (__po_hi_request_t* request);

/*  Periodic task : Pinger*/

void* pinger_job ();

void __po_hi_main_deliver 
      (__po_hi_msg_t* message);

#endif
