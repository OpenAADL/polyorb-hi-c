/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2011, European Space Agency.
 */

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
   return __PO_HI_NOTIMPLEMENTED;
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
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_packet_store_write (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t* packet)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_packet_store_free (__po_hi_storage_packet_store_t* store, int n_free)
{
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_packet_store_status (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_store_status_t* status)
{
   return __PO_HI_NOTIMPLEMENTED;
}


