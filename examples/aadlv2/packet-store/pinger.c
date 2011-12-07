#include <stdio.h>
#include <request.h> 
#include <deployment.h> 

__po_hi_request_t pkt;


void user_produce_pkts_init ()
{
  printf ("*** INIT PACKET PRODUCER ***\n");
  fflush (stdout);
}



void user_produce_pkts ()
{
  static int p = 0;

  pkt.vars.pinger_global_data_source.pinger_global_data_source = p;
  pkt.port = pinger_global_data_source;

  printf ("*** PRODUCE PKT WITH VALUE *** %d\n", p);
  p++;
  fflush (stdout);
}


void user_do_ping_spg ()
{
  printf ("*** SENDING PKT *** \n");
  __po_hi_gqueue_store_out (node_a_pinger_k, pinger_local_data_source, &(pkt));
  fflush (stdout);
}

void recover (void)
{
  printf ("*** RECOVER ACTION ***\n");
  fflush (stdout);
}
