#include <stdio.h>
#include <request.h>
#include <deployment.h>
#include <po_hi_storage.h>
#include <po_hi_gqueue.h>

__po_hi_storage_packet_store_t packet_store;

void user_produce_pkts_init ()
{
  printf ("*** INIT PACKET PRODUCER ***\n");

  if (__po_hi_storage_packet_store_new (&packet_store) != __PO_HI_SUCCESS)
  {
      printf ("*** /!\ ERROR WHEN CREATING THE PACKET STORE /!\ ***\n");
  }
  fflush (stdout);
}

void user_produce_pkts ()
{
  static int p = 0;
  int ret;

  __po_hi_request_t pkt;
  pkt.vars.pinger_global_data_source.pinger_global_data_source = p;
  pkt.port = pinger_global_data_source;

  printf ("*** PRODUCE PKT WITH VALUE *** %d\n", p);
  p++;

  ret = __po_hi_storage_packet_store_write (&packet_store, &pkt);

  if (ret != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN WRITING A PACKET IN THE STORE (ret=%d) /!\\ ***\n", ret);
  }

  fflush (stdout);
}


void user_do_ping_spg ()
{

  int ret;
  __po_hi_request_t pkt;
  ret = __po_hi_storage_packet_store_read (&packet_store, &pkt);

  if (ret != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN READING A PACKET IN THE STORE /!\\ ***\n");

      if (ret == __PO_HI_UNAVAILABLE)
      {
         printf ("*** /!\\ ;_; NO PACKET AVAILABLE AT THIS TIME ;_; /!\\ ***\n");
      }
  }
  else
  {
      printf ("*** SENDING PKT *** \n");
      __po_hi_gqueue_store_out (node_a_pinger_k, pinger_local_data_source, &(pkt));
  }
  fflush (stdout);
}

void recover (void)
{
  printf ("*** RECOVER ACTION ***\n");
  fflush (stdout);
}
