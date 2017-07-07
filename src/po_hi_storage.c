/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2017 ESA & ISAE.
 */

#if defined (__CYGWIN__) || defined (__MINGW32__) || defined (RTEMS_POSIX) || defined (RTEMS_PURE) || defined (FREERTOS)
#else
#include <xlocale.h>
#endif
#include <string.h>

#include <po_hi_config.h>
#include <po_hi_debug.h>
#include <po_hi_storage.h>
#include <po_hi_returns.h>

/*
 * Files operations
 */

int __po_hi_storage_file_open (const char* filename, __po_hi_storage_file_t* file)
{
   int len;
   int fd;

   if (file == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_open: invalid file argument\n");
      return __PO_HI_INVALID;
   }

   len = strlen (filename);

   memset (file->filename, 0, __PO_HI_STORAGE_FILENAME_MAXLENGTH);

   if (len >= __PO_HI_STORAGE_FILENAME_MAXLENGTH)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_open: file failed to be opened\n");
      return __PO_HI_INVALID;
   }

   strncpy (file->filename, filename, len);

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   /*
    * If the file already exist, we open it for reading/writing
    */

   fd = open (filename, O_RDWR | O_SYNC);

   if (fd == -1)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_open: warning, file %s does not exist, continue anyway\n", filename);
   }
   else
   {
      file->fd = fd;
   }

   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}


int __po_hi_storage_file_close (__po_hi_storage_file_t* file)
{
   if ( (file == NULL) || (file->filename == NULL))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_close: invalid file argument\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (file->fd == -1)
   {
      __DEBUGMSG ("[STORAGE] Warning, file %s does not exist, continue anyway\n", file->filename);
      return __PO_HI_INVALID;
   }

   if ( close (file->fd))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_close: %s cannot close file\n", file->filename);
      return __PO_HI_ERROR_UNKNOWN;
   }

   file->fd = -1;

   return __PO_HI_SUCCESS;
#endif

   return __PO_HI_NOTIMPLEMENTED;
}


int __po_hi_storage_file_create (__po_hi_storage_file_t* file)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct stat ss;
   int fd;
#endif

   if ((file == NULL) || (file->filename == NULL))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_create: invalid file parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (stat (file->filename, &ss) == 0)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_create: file %s already exists\n", file->filename);
      return __PO_HI_ERROR_EXISTS;
   }

   /*
    * We assume the file is not open previously by a call to open().
    * Otherwise, we assume this is an error.
    */
   if (file->fd != -1)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_create: file already opened (%d)\n", file->fd);
   }

   fd = open (file->filename, O_RDWR | O_CREAT | O_SYNC, S_IRWXU | S_IRGRP | S_IROTH);

   if (fd == -1)
   {
      __DEBUGMSG ("[STORAGE] Warning, cannot open file %s with create attributes\n", file->filename);
      return __PO_HI_INVALID;
   }

   file->fd = fd;

   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_read (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   int n;

   if ((file == NULL) || (file->filename == NULL))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_read: invalid file parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (file->fd == -1)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_read: invalid file handle (%d)\n", file->fd);
      return __PO_HI_INVALID;
   }

   n = read (file->fd, buf, bufsize);

   if (n != bufsize)
   {
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_write (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   int n;

   if ((file == NULL) || (file->filename == NULL))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_write: invalid file parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (file->fd == -1)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_write: invalid file handle (%d)\n", file->fd);
      return __PO_HI_INVALID;
   }

   n = write (file->fd, buf, bufsize);

   if (n != bufsize)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_write: invalid buffer size\n");
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_delete (const __po_hi_storage_file_t* file)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct stat ss;
#endif

   if ((file == NULL) || (file->filename == NULL))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_delete: invalid file parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (stat (file->filename, &ss) != 0)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_delete: file does not exist\n");
      return __PO_HI_ERROR_EXISTS;
   }

   if (file->fd != -1)
   {
      if (close (file->fd))
      {
         __DEBUGMSG ("[STORAGE] __po_hi_storage_file_delete: error when trying to close the file (fd=%d)\n", file->fd);
         return __PO_HI_ERROR_UNKNOWN;
      }
   }

   if (unlink (file->filename))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_delete: error when trying to delete the file\n");
      return __PO_HI_ERROR_UNKNOWN;
   }
   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_rename (const __po_hi_storage_file_t* oldfile, const __po_hi_storage_file_t* newfile)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct stat ss;
#endif

   if ((oldfile == NULL) || (oldfile->filename == NULL))
   {
      return __PO_HI_INVALID;
   }

   if ((newfile == NULL) || (newfile->filename == NULL))
   {
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (stat (newfile->filename, &ss) == 0)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_rename: destination file %s already exists\n", newfile->filename);
      return __PO_HI_ERROR_EXISTS;
   }

   if (stat (oldfile->filename, &ss))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_rename: source file %s does not exist\n", oldfile->filename);
      return __PO_HI_ERROR_NOEXISTS;
   }

   if (! S_ISREG (ss.st_mode))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_rename: source file %s is not a regular file\n", oldfile->filename);
      return __PO_HI_ERROR_NOEXISTS;
   }

   if (rename (oldfile->filename, newfile->filename))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_rename: error when trying to delete old file\n");
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif

   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_file_append (const __po_hi_storage_file_t* file, char* buf, int bufsize)
{
   int ret;

   if ((file == NULL) || (file->filename == NULL))
   {
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (file->fd == -1)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_append: file %s does not have an appropriate descriptor\n", file->filename);
      return __PO_HI_INVALID;
   }

   if (lseek (file->fd, 0, SEEK_END))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_append: error when trying to set file offset\n");
      return __PO_HI_ERROR_UNKNOWN;
   }

   ret = write (file->fd, buf, bufsize);

   if (ret != bufsize)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_file_append: cannot write %d bytes\n", bufsize);
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_file_replace (const __po_hi_storage_file_t* oldfile, const __po_hi_storage_file_t* newfile)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_file_lock (const __po_hi_storage_file_t* file)
{

   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_file_unlock (const __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

/*
 * Directory operations
 */

int __po_hi_storage_directory_open (const char* dirname, __po_hi_storage_dir_t* dir)
{
   int len;

   if (dirname == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_open: invalid directory parameter\n");
      return __PO_HI_INVALID;
   }

   if (dir == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_open: invalid directory parameter\n");
      return __PO_HI_INVALID;
   }

   len = strlen (dirname);

   if (len >= __PO_HI_STORAGE_FILENAME_MAXLENGTH)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_open: name too long\n");
      return __PO_HI_INVALID;
   }

   memset (dir->dirname, 0, __PO_HI_STORAGE_FILENAME_MAXLENGTH);

   memcpy (dir->dirname, dirname, len);

   dir->nb_files = 0;

   return __PO_HI_SUCCESS;
}

int __po_hi_storage_directory_create (const __po_hi_storage_dir_t* dir)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct stat ss;
#endif

   if (dir == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_create: invalid directory parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (stat (dir->dirname, &ss))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_create: file already exists\n");
      return __PO_HI_ERROR_EXISTS;
   }

   if (mkdir (dir->dirname, S_IRWXU | S_IRGRP | S_IROTH))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_create: mkdir error\n");
      return __PO_HI_INVALID;
   }
   return __PO_HI_SUCCESS;
#endif

   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_delete (const __po_hi_storage_dir_t* dir)
{
   if (dir == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_delete: invalid directory parameter\n");
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (rmdir (dir->dirname))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_delete: rmdir error\n");
      return __PO_HI_INVALID;
   }
   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_rename (const __po_hi_storage_dir_t* olddir, const __po_hi_storage_dir_t* newdir)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct stat ss;
#endif

   if ((olddir == NULL) || (olddir->dirname == NULL))
   {
      return __PO_HI_INVALID;
   }

   if ((newdir == NULL) || (newdir->dirname == NULL))
   {
      return __PO_HI_INVALID;
   }

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (stat (newdir->dirname, &ss) == 0)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_rename: destination directory %s already exists\n", newdir->dirname);
      return __PO_HI_ERROR_EXISTS;
   }

   if (stat (olddir->dirname, &ss))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_rename: source directory %s does not exist\n", olddir->dirname);
      return __PO_HI_ERROR_NOEXISTS;
   }

   if (! S_ISDIR (ss.st_mode))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_rename: source directory %s is not a directory\n", olddir->dirname);
      return __PO_HI_ERROR_NOEXISTS;
   }

   if (rename (olddir->dirname, newdir->dirname))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_rename: error when trying to rename\n");
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif

   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_directory_list (__po_hi_storage_dir_t* dir)
{
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   struct dirent* ent;
   DIR*           sdir;

#endif

   if ((dir == NULL) || (dir->dirname == NULL))
   {
      return __PO_HI_INVALID;
   }


#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   sdir = opendir (dir->dirname);

   if (sdir == NULL)
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_list: fail to call opendir on %s\n", dir->dirname);
      return __PO_HI_ERROR_NOEXISTS;
   }

   dir->nb_files = 0;

   while ( ( ( ent = readdir (sdir) ) != NULL ) && (dir->nb_files < __PO_HI_STORAGE_DIRECTORY_MAXFILES) )
   {
      int n = dir->nb_files;
      int len = strlen (ent->d_name);
      if (len < __PO_HI_STORAGE_FILENAME_MAXLENGTH)
      {
         n = dir->nb_files;
         memset (dir->filename[n], 0, __PO_HI_STORAGE_FILENAME_MAXLENGTH);
         memcpy (dir->filename[n], ent->d_name, len);
         dir->nb_files++;
      }
      else
      {
         __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_list: invalid filename %s\n", ent->d_name);
      }
   }

   if (closedir (sdir))
   {
      __DEBUGMSG ("[STORAGE] __po_hi_storage_directory_list: fail to call closedir on %s\n", dir->dirname);
      return __PO_HI_ERROR_UNKNOWN;
   }

   return __PO_HI_SUCCESS;
#endif

   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_directory_lock (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_directory_unlock (const __po_hi_storage_dir_t* dir)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

int __po_hi_storage_change_cdir (__po_hi_storage_dir_t* new_current_directory)
{
   if ( (new_current_directory == NULL) || (new_current_directory->dirname == NULL))
   {
      return __PO_HI_INVALID;
   }
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   if (chdir (new_current_directory->dirname))
   {
      return __PO_HI_ERROR_NOEXISTS;
   }
   return __PO_HI_SUCCESS;
#endif
   return __PO_HI_NOTIMPLEMENTED;
}

int __po_hi_storage_get_cdir (__po_hi_storage_dir_t* current_directory)
{
   if ( (current_directory == NULL) || (current_directory->dirname == NULL))
   {
      return __PO_HI_INVALID;
   }
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   memset (current_directory->dirname, 0, __PO_HI_STORAGE_FILENAME_MAXLENGTH);

   if (getcwd (current_directory->dirname, __PO_HI_STORAGE_FILENAME_MAXLENGTH) == NULL)
   {
      return __PO_HI_ERROR_UNKNOWN;
   }
   return __PO_HI_SUCCESS;
#endif

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
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_packet_store_new_from_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
int __po_hi_storage_packet_store_write_to_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file)
{
   return __PO_HI_NOTIMPLEMENTED;
}
#pragma GCC diagnostic pop

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
