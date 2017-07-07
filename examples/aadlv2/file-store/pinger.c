#include <stdio.h>
#include <request.h>
#include <deployment.h>
#include <po_hi_storage.h>
#include <po_hi_gqueue.h>

#define FILENAME "pinger.dat"

__po_hi_storage_file_t myfile_read;
__po_hi_storage_file_t myfile_write;

void user_produce_pkts_init ()
{
  printf ("*** INIT DATA PRODUCER ***\n");

  if (__po_hi_storage_file_open (FILENAME, &myfile_write) != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN OPENING THE FILE %s /!\\ ***\n", FILENAME);
  }

  if (__po_hi_storage_file_create (&myfile_write) != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN CREATING THE FILE %s /!\\ ***\n", FILENAME);
  }

  if (__po_hi_storage_file_open (FILENAME, &myfile_read) != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN OPENING THE FILE %s /!\\ ***\n", FILENAME);
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

  ret = __po_hi_storage_file_write (&myfile_write, &pkt, sizeof (__po_hi_request_t));

  if (ret != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN WRITING A PACKET IN THE FILE (ret=%d) /!\\ ***\n", ret);
  }


  fflush (stdout);
}


void user_do_ping_spg ()
{

  int ret;
  __po_hi_request_t pkt;

  ret = __po_hi_storage_file_read (&myfile_read, &pkt, sizeof (__po_hi_request_t));


  if (ret != __PO_HI_SUCCESS)
  {
      printf ("*** /!\\ ERROR WHEN READING A PACKET FROM FILE /!\\ ***\n");

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
