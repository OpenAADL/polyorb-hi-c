/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2011-2014 ESA & ISAE.
 */

#ifndef __PO_HI_STORAGE_H__
#define __PO_HI_STORAGE_H__

#include <po_hi_types.h>
#include <deployment.h>
#include <request.h>

#include <deployment.h>
/* included files from the generated code */

#include <po_hi_config.h>
#include <po_hi_returns.h>
#include <po_hi_monitor.h>
#include <po_hi_time.h>
#include <po_hi_task.h>
#include <po_hi_debug.h>
#include <po_hi_protected.h>
#include <po_hi_utils.h>


#ifndef __PO_HI_STORAGE_FILENAME_MAXLENGTH
#define __PO_HI_STORAGE_FILENAME_MAXLENGTH 100
#endif

#ifndef __PO_HI_STORAGE_DIRECTORY_MAXFILES
#define __PO_HI_STORAGE_DIRECTORY_MAXFILES 100
#endif

#ifndef __PO_HI_STORAGE_PACKET_SIZE
#define __PO_HI_STORAGE_PACKET_SIZE sizeof(__po_hi_request_t)
#endif


#ifndef __PO_HI_STORAGE_MAX_PACKETS
#define __PO_HI_STORAGE_MAX_PACKETS 100
#endif

#ifndef __PO_HI_STORAGE_MAX_PACKET_STORES
#define __PO_HI_STORAGE_MAX_PACKET_STORES 100
#endif

#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#endif

typedef struct
{
   int         file_id;
   char        filename[__PO_HI_STORAGE_FILENAME_MAXLENGTH];
#if defined (POSIX) || defined (RTEMS_POSIX) || defined (XENO_POSIX)
   int         fd;
#endif
} __po_hi_storage_file_t;

typedef struct
{
   int         dir_id;
   int         nb_files;
   char        dirname[__PO_HI_STORAGE_FILENAME_MAXLENGTH];
   char        filename[__PO_HI_STORAGE_DIRECTORY_MAXFILES][__PO_HI_STORAGE_FILENAME_MAXLENGTH];
} __po_hi_storage_dir_t;

#ifndef __PO_HI_STORAGE_PACKET_SIZE
#define __PO_HI_STORAGE_PACKET_SIZE sizeof(__po_hi_request_t __po_hi_storage_packet_t)
#endif

typedef __po_hi_uint8_t __po_hi_storage_packet_t;

typedef struct
{
   __po_hi_uint8_t            packets[__PO_HI_STORAGE_PACKET_SIZE * __PO_HI_STORAGE_MAX_PACKETS];    /*< packets contained int he store (structured bytes)  >*/
   int                        n_packets;                               /*< amount of packets stored in the store                                            >*/
   int                        capacity;                                /*< actual size of the store, meaning the number of packets it can store             >*/
   int                        read_off;                                /*< read offset in the buffer in terms of number of packets                          >*/
   int                        write_off;                               /*< write offset in the buffer in terns of number of packets                         >*/
   __po_hi_mutex_t            mutex;                                   /*< ensure buffer protection from concurrent accesses                                >*/
} __po_hi_storage_packet_store_t;


typedef struct
{
   __po_hi_uint32_t    n_packets;   /*< number of packets in the store >   */
   __po_hi_uint32_t    n_avail;     /*< available packets size >           */
   __po_hi_uint8_t     full;        /*< is the store full ?>               */
}__po_hi_storage_packet_store_status_t;

/*
 * Files operations
 */

/**
 * \fn __po_hi_storage_file_open
 *
 * \brief Open a file designated as filename and complete the content of the
 * second parameter.
 *
 * Please note that this function just fills the structure passed as the
 * second parameter. It does not create the file, this is supposed to be
 * done by a separate function.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS: successful operation
 *  - __PO_HI_TOOMANY: too may files are open at this time, cannot open more.
 *  - __PO_HI_INVALID: supplied filename is invalid (invalid characters or too long)
 */
int __po_hi_storage_file_open (const char* filename, __po_hi_storage_file_t*);

/**
 * \fn __po_hi_storage_file_create
 *
 * \brief Create the file on the filesystem.
 *
 * This function creates the file with the properties stored in the
 * second argument. The argument is the file to create.
 * The function can return the following values:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_ERROR_EXISTS     : File already exists
 * - __PO_HI_INVALID          : Invalid file
 */
int __po_hi_storage_file_create (__po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_file_read
 *
 * \brief Read part of a file.
 *
 * This function read a fixed length (part of) a file and
 * stores the content in a buffer. First argument is a file 
 * (previously opened with __po_hi_storage_file_open() ), the
 * second argument is the buffer to store the file content
 * while the last argument is the size to be read.
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file
 */
int __po_hi_storage_file_read (const __po_hi_storage_file_t* file, char* buf, int bufsize);

/**
 * \fn __po_hi_storage_file_write
 *
 * \brief Write part of a file.
 *
 * This function write a buffer in a file, at offset 0. 
 * First argument is a file 
 * (previously opened with __po_hi_storage_file_open() ), the
 * second argument is the buffer to write
 * while the last argument is the size to be written.
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file
 */
int __po_hi_storage_file_write (const __po_hi_storage_file_t* file, char* buf, int bufsize);

/**
 * \fn __po_hi_storage_file_delete
 *
 * \brief Delete a file.
 *
 * This function delete a file. The first argument is the file to be deleted
 * (previously opened with __po_hi_storage_file_open() ).
 * Result code are the following:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file
 * - __PO_HI_ERROR_NOEXISTS   : The file does not exists
 */
int __po_hi_storage_file_delete (const __po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_file_rename
 *
 * \brief Rename a file.
 *
 * This function renames a file. The first argument is the original file
 * and the second argument the destination file.
 * (both were reviously opened with __po_hi_storage_file_open() ).
 * This function assumes there is no file that has already the name of the
 * second argument.
 *
 * Result code are the following:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file (either source or destination)
 * - __PO_HI_ERROR_NOEXISTS   : The source file (first argument) does not exists
 * - __PO_HI_ERROR_EXISTS     : The destination file (second argument) already
 *                              exists.
 */
int __po_hi_storage_file_rename (const __po_hi_storage_file_t* oldfile, const __po_hi_storage_file_t* newfile);

/**
 * \fn __po_hi_storage_file_append
 *
 * \brief Append content to a file.
 *
 * This function appends some data to an existing file.
 * This is as writting data at the last offset of the file.
 * First argument is a file (previously opened with 
 * __po_hi_storage_file_open() ), the
 * second argument is the buffer to write
 * while the last argument is the size to be written.
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file
 */
int __po_hi_storage_file_append (const __po_hi_storage_file_t* file, char* buf, int bufsize);

/**
 * \fn __po_hi_storage_file_replace
 *
 * \brief Replace a file.
 *
 * This function replace a file with another one. The first argument is the original file
 * and the second argument the file to be replaced.
 * (both were reviously opened with __po_hi_storage_file_open() ).
 * This function assumes there is already one file labelled under the
 * destination file.
 *
 * Result code are the following:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_ERROR_UNKNOWN    : Unknown error
 * - __PO_HI_INVALID          : Invalid file (either source or destination)
 * - __PO_HI_ERROR_NOEXISTS   : The source or destination file does not exists
 */
int __po_hi_storage_file_replace (const __po_hi_storage_file_t* oldfile, const __po_hi_storage_file_t* newfile);


/**
 * \fn __po_hi_storage_file_lock
 *
 * \brief Lock a file
 *
 * This function locks a file, it acquires a lock on the file so that it
 * ensures that only one task is operating on it. If a call is issued while
 * the lock was already acquired, the second call will be put in the waiting
 * queue, waiting for the file to be unlocked. The behavior is basically like
 * a mutex.
 *
 * Result code are the following:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_INVALID          : Invalid file
 */
int __po_hi_storage_file_lock (const __po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_file_unlock
 *
 * \brief Unlock a file
 *
 * This function unlocks a file, it releases a lock on the specified file.
 * The lock hqs to be acquired before using __po_hi_storage_file_lock().
 * Please note that calling this function when the file was not locked
 * results in an error.
 *
 * Result code are the following:
 * - __PO_HI_SUCCESS          : Successful operation
 * - __PO_HI_INVALID          : Invalid file
 * - __PO_HI_UNAVAILABLE      : The file was not locked.
 */

int __po_hi_storage_file_unlock (const __po_hi_storage_file_t* file);


/*
 * Directory operations
 */

/**
 * \fn __po_hi_storage_directory_open
 *
 * \brief Open a directory designated under the name associated in the first
 * parameter. The second parameter is the directory structure to be
 * initialized.
 *
 * Please note that this function just fills the structure passed as the
 * second parameter. It does not create the directory itself
 * on the real filesystem, this is supposed to be done by a separate 
 * function (__po_hi_storage_directory_create).
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS: successful operation
 *  - __PO_HI_TOOMANY: too may directories are open at this time, cannot open more.
 *  - __PO_HI_INVALID: supplied directory name is invalid
 */
int __po_hi_storage_directory_open (const char*, __po_hi_storage_dir_t*);

/**
 * \fn __po_hi_storage_directory_create
 *
 * \brief Create a directory.
 *
 * Create a directory designated in the first parameter (previously
 * created using the __po_hi_storage_directory_open() function).
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_ERROR_EXISTS       : directory already exists
 */
int __po_hi_storage_directory_create (const __po_hi_storage_dir_t*);

/**
 * \fn __po_hi_storage_directory_delete
 *
 * \brief Delete a directory.
 *
 * Delete a directory designated in the first parameter (previously
 * created using the __po_hi_storage_directory_open() function).
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_ERROR_NOEXISTS     : directory does not exist
 */
int __po_hi_storage_directory_delete (const __po_hi_storage_dir_t*);

/**
 * \fn __po_hi_storage_directory_rename
 *
 * \brief Rename a directory.
 *
 * Rename a directory designated in the first parameter (previously
 * created using the __po_hi_storage_directory_open() function) with
 * the name of the directory supplied in the second argument
 * (also created using the __po_hi_storage_directory_open() function).
 * After successful call, the directory will not be available under the name
 * of the first argument.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_ERROR_NOEXISTS     : directory of the first parameter does not
 *                                 exist
 *  - __PO_HI_ERROR_EXISTS       : directory of the second parameter already
 *                                 exist
 */
int __po_hi_storage_directory_rename (const __po_hi_storage_dir_t* olddir, const __po_hi_storage_dir_t* newdir);

/**
 * \fn __po_hi_storage_directory_list
 *
 * \brief List the content of the directory.
 *
 * This function fills the __po_hi_storage_dir_t structure
 * passed as argument with all the necessary content (files
 * contained in the directory, etc.).
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_ERROR_NOEXISTS     : the directory does not exist.
 */
int __po_hi_storage_directory_list (__po_hi_storage_dir_t* dir);

/**
 * \fn __po_hi_storage_directory_lock
 *
 * \brief Lock a directory.
 *
 * Lock a directory so that it ensures an exclusive access for
 * a task. It acts as a mutex: if the lock was already acquired,
 * a second call will make the second caller waiting for the lock to be
 * released.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 */
int __po_hi_storage_directory_lock (const __po_hi_storage_dir_t* dir);

/*
 * \fn __po_hi_storage_file_close
 *
 * \brief Close a file
 *
 * Close a file that was previously opened using __po_hi_storage_file_open().
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 */

int __po_hi_storage_file_close (__po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_directory_unlock
 *
 * \brief Unlock a directory.
 *
 * Unlock a previously locked directory. It releases the mutex associated
 * to the mutex so that other task can locks the resource again.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_UNAVAILABLE        : the directory was not locked.
 */
int __po_hi_storage_directory_unlock (const __po_hi_storage_dir_t* dir);

/**
 * \fn __po_hi_storage_change_cdir
 *
 * \brief Change the current directory of a task
 *
 * Change the directory associated with the current execution
 * context of the task.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid directory structure
 *  - __PO_HI_NOEXISTS           : the directory does not exists
 */
int __po_hi_storage_change_cdir (__po_hi_storage_dir_t* new_current_directory);

/**
 * \fn __po_hi_storage_get_cdir
 *
 * \brief Get the current directory of the operating task
 *
 * Change the directory associated with the current execution
 * context of the task.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 */
int __po_hi_storage_get_cdir (__po_hi_storage_dir_t* current_directory);


/*
 * Packets service
 */

/**
 * \fn __po_hi_storage_packet_store_new
 *
 * \brief Create a new packet store
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_ERROR_MUTEX_INIT   : error when trying to instantiate locking-related resources
 *  - __PO_HI_TOOMANY            : too many store already created
 */
int __po_hi_storage_packet_store_new (__po_hi_storage_packet_store_t* store);

/**
 * \fn __po_hi_storage_packet_store_new_from_file
 *
 * \brief Create a new packet store with the data stored in a file.
 *
 * The first argument is the store that would contain the packets
 * while the second argument is the file that contain the packet
 * store data (created during a previous execution with
 * __po_hi_storage_packet_store_zrite_to_file ())
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_TOOMANY            : too many store already created
 *  - __PO_HI_NOEXISTS           : file does not exists (second argument)
 */
int __po_hi_storage_packet_store_new_from_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_packet_store_write_to_file
 *
 * \brief Write the content of a packet store to a file.
 *
 * The first argument is the store that would contain the packets
 * while the second argument is the file that would be created.
 * This functions assumes the destination file does not exists.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_TOOMANY            : too many store already created
 *  - __PO_HI_EXISTS             : file already exists (second argument)
 */
int __po_hi_storage_packet_store_write_to_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file);

/**
 * \fn __po_hi_storage_packet_store_read
 *
 * \brief Read a packet from a packet store.
 *
 * The first argument is the store while the second argument
 * is the packet to be read (contain the information/data of 
 * the packet). If the store does not contain any packet, the function
 * returns an error.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_UNAVAILABLE        : no packet to be read.
 *  - __PO_HI_INVALID            : invalid packet store or packet to write
 *                                 (invalid address)
 */
int __po_hi_storage_packet_store_read (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t*);

/**
 * \fn __po_hi_storage_packet_store_write
 *
 * \brief Write a packet to a packet store.
 *
 * The first argument is the store while the second argument
 * is the packet to be written (contain the information/data of 
 * the packet). 
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_TOOMANY            : the store contains already too many
 *                                 packets, cannot write more packets.
 *  - __PO_HI_ERROR_MUTEX_LOCK   : error when trying to acquire the mutex
 *                                 associated with the packet store.
 *  - __PO_HI_ERROR_MUTEX_UNLOCK : error when trying to release the mutex
 *                                 associated with the packet store.
 *  - __PO_HI_INVALID            : invalid packet store or packet to write
 *                                 (invalid address)
 */
int __po_hi_storage_packet_store_write (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t*);

/**
 * \fn __po_hi_storage_packet_store_free
 *
 * \brief Free old packets from a store.
 *
 * The first argument is the store while the second argument
 * is the number of packets to free. 
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_NOEXISTS           : the user ask to free more packets
 *                                 than the quantity of available in the
 *                                 store. So, all packets are free'ed and the
 *                                 function returns __PO_HI_NOEXISTS.
 *  - __PO_HI_INVALID            : invalid packet store or packet to write
 *                                 (invalid address)
 */
int __po_hi_storage_packet_store_free (__po_hi_storage_packet_store_t* store, int n_free);

/**
 * \fn __po_hi_storage_packet_store_status
 *
 * \brief Indicate the status of a packet store.
 *
 * The first argument is the store while the second argument
 * is the status structure that would be filled by the function.
 *
 * Upon success, the function returns __PO_HI_SUCCESS.
 * It returns the following potential values:
 *  - __PO_HI_SUCCESS            : successful operation
 *  - __PO_HI_INVALID            : invalid packet store or invalid structure
 *                                 (invalid address)
 */
int __po_hi_storage_packet_store_status (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_store_status_t* status);

#endif /* __PO_HI_STORAGE_H__ */
