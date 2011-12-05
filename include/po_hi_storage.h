/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://assert-project.net/taste
 *
 * Copyright (C) 2011, European Space Agency.
 */

#ifndef __PO_HI_STORAGE_H__
#define __PO_HI_STORAGE_H__

#ifndef __PO_HI_FILENAME_MAXLENGTH
#define __PO_HI_FILENAME_MAXLENGTH 100
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



typedef struct
{
   int         file_id;
   char        filename[__PO_HI_STORAGE_FILENAME_MAXLENGTH];
} __po_hi_storage_file_t;

typedef struct
{
   int         dir_id;
   char        filename[__PO_HI_STORAGE_DIRECTORY_MAXFILES][__PO_HI_FILENAME_MAXLENGTH];
} __po_hi_storage_dir_t;

typedef __po_hi_request_t __po_hi_storage_packet_t;

typedef struct
{
   __po_hi_storage_packet_t packets[__PO_HI_STORAGE_MAX_PACKETS];
} __po_hi_storage_packet_store_t;


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
 *  - __PO_HI_INVALID: supplied filename is invalid
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
int __po_hi_storage_file_create (const __po_hi_storage_file_t* file);

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
int __po_hi_storage_file_rename (const __po_hi_storage_file_t* oldfile,const __po_hi_storage_file_t* newfile);

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
int __po_hi_storage_file_replace (const __po_hi_storage_file_t* oldfile, const __po_hi_file_t* newfile);


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

int __po_hi_storage_directory_open (const char*, __po_hi_storage_dir_t*);

int __po_hi_storage_directory_create (const __po_hi_storage_dir_t*);

int __po_hi_storage_directory_delete (const __po_hi_storage_dir_t*);

int __po_hi_storage_directory_rename (const __po_hi_storage_dir_t* oldname, const __po_hi_storage_dir_t* newname);

int __po_hi_storage_directory_list (const __po_hi_storage_dir_t* dir);

int __po_hi_storage_directory_lock (const __po_hi_storage_dir_t* dir);

int __po_hi_storage_directory_unlock (const __po_hi_storage_dir_t* dir);

int __po_hi_storage_change_cdir (__po_hi_storage_dir_t* new_current_directory);

int __po_hi_storage_get_cdir (__po_hi_storage_dir_t* current_directory);


/*
 * Packets service
 */

int __po_hi_storage_packet_store_new (__po_hi_storage_packet_store_t* store);

int __po_hi_storage_packet_store_new_from_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file);

int __po_hi_storage_packet_store_write_to_file (__po_hi_storage_packet_store_t* store, __po_hi_storage_file_t* file);

int __po_hi_storage_packet_store_read (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t*);

int __po_hi_storage_packet_store_write (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_t*);

int __po_hi_storage_packet_store_free (__po_hi_storage_packet_store_t* store, int n_free);

int __po_hi_storage_packet_store_status (__po_hi_storage_packet_store_t* store, __po_hi_storage_packet_store_status_t* status);


#endif /* __PO_HI_STORAGE_H__ */

