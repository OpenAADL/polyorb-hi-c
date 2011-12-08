/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2011, European Space Agency.
 */

#include <string.h>
#include <po_hi_debug.h>
#include <po_hi_storage.h>
#include <po_hi_returns.h>

/*
 * Files operations
 */

int __po_hi_storage_file_open (const char* filename, __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_create (const __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_read (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_write (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_delete (const __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_rename (const __po_hi_storage_file_t* oldfile,const __po_hi_storage_file_t* newfile)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_append (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_replace (const __po_hi_storage_file_t* oldfile, const __po_hi_storage_file_t* newfile)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_lock (const __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_unlock (const __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

/*
 * Directory operations
 */

int __po_hi_storage_directory_open (const char* dirname, __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_create (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_delete (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_rename (const __po_hi_storage_dir_t* oldname, const __po_hi_storage_dir_t* newname)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_list (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_lock (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_unlock (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_change_cdir (__po_hi_storage_dir_t* new_current_directory)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_get_cdir (__po_hi_storage_dir_t* current_directory)
{
   return __PO_HI_NOTIMPLEMENTED;
}


/*
 * Packets service
 */

int __po_hi_storage_packet_store_new (__po_hi_storage_packet_store_t* store)
{
   if (__po_hi_mutex_init (&store->mutex, __PO_HI_MUTEX_REGULAR, 0) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_CREATE;
   }
   store->capacity   = __PO_HI_STORAGE_MAX_PACKETS;
   store->n_packets  = 0;
   store->read_off   = 0;
   store->write_off  = 0;
   return __PO_HI_SUCCESS;
}

int __po_hi_storage_packet_store_new_from_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_packet_store_write_to_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_packet_store_read (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t* packet)
{
   int retcode = __PO_HI_ERROR_UNKNOWN;

   if (store == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_read: store is NULL\n");
      return __PO_HI_INVALID;
   }

   if (packet == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_read: packet is NULL\n");
      return __PO_HI_INVALID;
   }

   if (__po_hi_mutex_lock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_LOCK;
   }

   if (store->n_packets < 1)
   {
      retcode = __PO_HI_UNAVAILABLE;
   }
   else
   {
      memcpy (packet, &(store->packets[store->read_off * __PO_HI_STORAGE_PACKET_SIZE]), __PO_HI_STORAGE_PACKET_SIZE);

      store->read_off   = (store->read_off + 1 % store->capacity);
      store->n_packets  = store->n_packets - 1;

      retcode = __PO_HI_SUCCESS;
   }

   if (__po_hi_mutex_unlock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
   return retcode;
}

int __po_hi_storage_packet_store_write (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t* packet)
{
   int retcode = __PO_HI_ERROR_UNKNOWN;

   if (store == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_write: store is NULL\n");
      return __PO_HI_INVALID;
   }

   if (packet == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_write: packet is NULL\n");
      return __PO_HI_INVALID;
   }

   if (__po_hi_mutex_lock (&store->mutex) != __PO_HI_SUCCESS)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_write: cannot lock mutex\n");
      return __PO_HI_ERROR_MUTEX_LOCK;
   }

   if (store->n_packets >= store->capacity)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_write: store is full\n");
      retcode = __PO_HI_TOOMANY;
   }
   else
   {
      memcpy (&(store->packets[store->write_off * __PO_HI_STORAGE_PACKET_SIZE]), packet, __PO_HI_STORAGE_PACKET_SIZE);

      store->write_off  = (store->write_off + 1 % store->capacity);
      store->n_packets  = store->n_packets + 1;

      retcode = __PO_HI_SUCCESS;
   }

   if (__po_hi_mutex_unlock (&store->mutex) != __PO_HI_SUCCESS)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_packet_store_write: cannot unlock mutex\n");
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
   return retcode;
}

int __po_hi_storage_packet_store_free (__po_hi_storage_packet_store_t* store, int n_free)
{
   int retcode = __PO_HI_ERROR_UNKNOWN;

   if (store == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (n_free == 0)
   {
      return __PO_HI_INVALID;
   }

   if (__po_hi_mutex_lock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_LOCK;
   }

   if (store->n_packets < n_free)
   {
      retcode = __PO_HI_UNAVAILABLE;
   }
   else
   {
      store->read_off   = (store->read_off + n_free % store->capacity);
      store->n_packets  = store->n_packets - n_free;

      retcode = __PO_HI_SUCCESS;
   }

   if (__po_hi_mutex_unlock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
   return retcode;
}

int __po_hi_storage_packet_store_status (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_store_status_t* status)
{
   if (store == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (status == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (__po_hi_mutex_lock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_LOCK;
   }

   status->n_packets = store->n_packets;
   status->n_avail   = store->capacity - store->n_packets;
   status->full = (store->n_packets == store->capacity) ? 1 : 0;

   if (__po_hi_mutex_unlock (&store->mutex) != __PO_HI_SUCCESS)
   {
      return __PO_HI_ERROR_MUTEX_UNLOCK;
   }
   return __PO_HI_SUCCESS;
}


