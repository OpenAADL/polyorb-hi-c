#ifndef __OCARINA_GENERATED_ACTIVITY_H_
#define __OCARINA_GENERATED_ACTIVITY_H_ 
#include <request.h>
/*****************************************************/

/*  This file was automatically generated by Ocarina */

/*  Do NOT hand-modify this file, as your            */

/*  changes will be lost when you re-run Ocarina     */

/*****************************************************/

void pinger_deliver 
    (__po_hi_request_t* request);

void* pinger_job (void);

void ping_me_deliver 
    (__po_hi_request_t* request);

void* ping_me_job (void);

void __po_hi_main_deliver 
    (__po_hi_request_t* request);

#endif
