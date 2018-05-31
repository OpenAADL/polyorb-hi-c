/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2018 ESA & ISAE.
 */

#include <deployment.h>
/* Generated code header */

#include <activity.h>
#include <marshallers.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_protected.h>
#include <po_hi_returns.h>

#include <po_hi_utils.h>
#include <drivers/po_hi_rtems_utils.h>

#include <po_hi_driver_drvmgr_common.h>
/* Common drvmgr initialization */

#include <drivers/po_hi_driver_serial_common.h>

#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <termios.h>
/* POSIX-style files */

#include <drivers/configuration/serial.h>

int po_hi_c_driver_rtems_drvmgr_serial_fd_read[__PO_HI_NB_DEVICES];
int po_hi_c_driver_rtems_drvmgr_serial_fd_write[__PO_HI_NB_DEVICES];

__po_hi_request_t    __po_hi_c_driver_rtems_drvmgr_serial_request;
__po_hi_msg_t        __po_hi_c_driver_rtems_drvmgr_serial_poller_msg;
__po_hi_mutex_t      __po_hi_c_rtems_serial_send_mutex;

/*!
 * \fn void __po_hi_c_driver_rtems_drvmgr_serial_poller (const __po_hi_device_id dev_id)
 * \brief Polling function for the RTEMS DRVMGR SERIAL.
 *
 * This function is the poller for the serial interface of the RTEMS DRVMGR SERIAL board.
 * It is supposed to be called by the underlying AADL code at a given period/rate.
 * The argument dev_id is the device_id handled by the device driver. By using
 * such an argument, we can use this function on a single node that uses several
 * driver instances (several serial interfaces connected to different serial buses).
 */

void __po_hi_c_driver_rtems_drvmgr_serial_poller (const __po_hi_device_id dev_id)
{
   int                  n;
   int                  ts;
   uint8_t*             ptr;

   ts = __PO_HI_MESSAGES_MAX_SIZE;
   ptr = &(__po_hi_c_driver_rtems_drvmgr_serial_poller_msg.content[0]);
   __po_hi_msg_reallocate (&__po_hi_c_driver_rtems_drvmgr_serial_poller_msg);
   while (ts > 0) {
     __PO_HI_DEBUG_DEBUG
       ("[DRVMGR SERIAL] Poller waits for incoming message (%d bytes are required)!\n", ts);
     n = read (po_hi_c_driver_rtems_drvmgr_serial_fd_read[dev_id], ptr, ts);

     __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] read() %d returns %d!\n",
                          po_hi_c_driver_rtems_drvmgr_serial_fd_read[dev_id], n);
     if (n == -1) {
       __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Cannot read on socket !\n");
       return;
     } else {
       ptr += n;
       ts -= n;
     }
   }

   __po_hi_c_driver_rtems_drvmgr_serial_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;

   __po_hi_unmarshall_request (&__po_hi_c_driver_rtems_drvmgr_serial_request,
                               &__po_hi_c_driver_rtems_drvmgr_serial_poller_msg);

   if (__po_hi_c_driver_rtems_drvmgr_serial_request.port > __PO_HI_NB_PORTS) {
     __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Invalid port number (%d), will not deliver",
                          __po_hi_c_driver_rtems_drvmgr_serial_request.port);
   }
   __po_hi_main_deliver (&__po_hi_c_driver_rtems_drvmgr_serial_request);
}

__po_hi_msg_t           __po_hi_c_driver_rtems_drvmgr_serial_sender_msg;

/*!
 * \fn int __po_hi_c_driver_rtems_drvmgr_serial_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
 * \brief Function related to the RTEMS DRVMGR SERIAL serial driver - sender function.
 *
 * This function implements the sender function to send bytes through the serial line using
 * the RTEMS DRVMGR SERIAL device.
 * There are the description of the arguments used by the function:
 *   - task_id: task that actually sends the data (emitter/producer task)
 *   - port   : (global) port that contains the data
 * It returns the following possible values :
 *   - __PO_HI_UNAVAILABLE : the driver does not handle the device connected to argument port.
 *   - __PO_HI_SUCCESS     : either no value was available to be sent or the function
 *                           send the message successfully over the network.
 */
int __po_hi_c_driver_rtems_drvmgr_serial_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int                     n;
   int                     ts;
   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;
   __po_hi_device_id       dev_id;

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id) {
     __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Invalid device id for sending\n");
     return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
     {
       __PO_HI_DEBUG_DEBUG
         ("[DRVMGR SERIAL] Send output task %d, port %d (local_port=%d): no value to send\n",
          task_id, port, local_port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);
   __po_hi_mutex_lock (&__po_hi_c_rtems_serial_send_mutex);
   __po_hi_msg_reallocate (&__po_hi_c_driver_rtems_drvmgr_serial_sender_msg);

   request->port = destination_port;
   __po_hi_marshall_request (request, &__po_hi_c_driver_rtems_drvmgr_serial_sender_msg);

   __PO_HI_DEBUG_DEBUG
     ("[DRVMGR SERIAL] Destination port= %d, msg size %d send through device %d (fd=%d)\n",
      destination_port,
      __po_hi_c_driver_rtems_drvmgr_serial_sender_msg.length,
      dev_id, po_hi_c_driver_rtems_drvmgr_serial_fd_write[dev_id]);

   n = write (po_hi_c_driver_rtems_drvmgr_serial_fd_write[dev_id],
              &__po_hi_c_driver_rtems_drvmgr_serial_sender_msg,
              __PO_HI_MESSAGES_MAX_SIZE);

   __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] write() returns %d\n", n);
   __po_hi_mutex_unlock (&__po_hi_c_rtems_serial_send_mutex);
   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}

/*!
 * \fn void __po_hi_c_driver_rtems_drvmgr_serial_init (__po_hi_device_id id)
 * \brief Initialization function for the RTEMS DRVMGR SERIAL serial driver.
 *
 * This function  is used to initialize the device driver connected to the
 * serial interface to a RTEMS DRVMGR SERIAL board. It uses the configuration properties
 * from its associated configuration parameters (using the
 * __po_hi_get_device_configuration function).
 */

void __po_hi_c_driver_rtems_drvmgr_serial_init (__po_hi_device_id id)
{
   uint32_t max_size;
   struct termios             oldtio,newtio;

   __po_hi_c_serial_conf_t* serialconf;

   /* Initializes drvmgr subsystem */

   __po_hi_c_driver_drvmgr_init ();

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL) {
     __PO_HI_DEBUG_INFO ("[DRVMGR SERIAL] Cannot get the name of the device !\n");
     return;
   }
   __po_hi_mutex_init (&__po_hi_c_rtems_serial_send_mutex,__PO_HI_MUTEX_REGULAR, 0);
   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_rtems_drvmgr_serial_sender);

   /* provide the spacewire driver with AMBA Plug&Play
    * info so that it can find the GRSPW cores.
    */

   __PO_HI_DEBUG_INFO ("[DRVMGR SERIAL] Initialization starts !\n");

   po_hi_c_driver_rtems_drvmgr_serial_fd_write[id] =
     po_hi_c_driver_rtems_drvmgr_serial_fd_read[id] = open (serialconf->devname, O_RDWR);

   if (po_hi_c_driver_rtems_drvmgr_serial_fd_read[id] < 0) {
     __PO_HI_DEBUG_CRITICAL ("[DRVMGR SERIAL] Error while opening device %s for reading\n",
                             serialconf->devname);
   }
   if (po_hi_c_driver_rtems_drvmgr_serial_fd_write[id] < 0) {
     __PO_HI_DEBUG_CRITICAL ("[DRVMGR SERIAL] Error while opening device %s for writing\n",
                             serialconf->devname);
   }

   __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Device opened for read (%s), fd=%d\n",
                        serialconf->devname , po_hi_c_driver_rtems_drvmgr_serial_fd_read[id]);
   __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Device opened for write (%s), fd=%d\n",
                        serialconf->devname , po_hi_c_driver_rtems_drvmgr_serial_fd_write[id]);

   tcgetattr (po_hi_c_driver_rtems_drvmgr_serial_fd_read[id], &oldtio);  /* save current serial port settings */
   tcgetattr (po_hi_c_driver_rtems_drvmgr_serial_fd_read[id], &newtio);  /* save current serial port settings */

   newtio.c_cflag |= CREAD ;
   newtio.c_iflag = IGNPAR | IGNBRK;
   newtio.c_lflag |= ICANON;
   newtio.c_cc[VMIN]=1;
   newtio.c_cc[VTIME]=0;
   cfmakeraw (&newtio);

   switch (__po_hi_c_driver_serial_common_get_speed (id))
     {
     case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200:
       newtio.c_cflag |= B19200;
       __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 19200\n");
       break;

     case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400:
       newtio.c_cflag |= B38400;
       __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 38400\n");
       break;

     case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600:
       newtio.c_cflag |= B57600;
       __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 57600\n");
       break;

     case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200:
       __PO_HI_DEBUG_DEBUG ("[LINUX SERIAL] Set speed to 115200\n");
       newtio.c_cflag |= B115200;
       break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON:
        __PO_HI_DEBUG_INFO ("[LINUX SERIAL] Unknwon speed for the serial line\n");
        break;
     }

   max_size = 1024;
#ifdef __PO_HI_MESSAGES_MAX_SIZE
   max_size = 4 * __PO_HI_MESSAGES_MAX_SIZE;
#endif

  if (tcflush (po_hi_c_driver_rtems_drvmgr_serial_fd_read[id], TCIOFLUSH) != 0) {
    __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Error when trying to flush read part\n");
  }

  if (tcflush (po_hi_c_driver_rtems_drvmgr_serial_fd_write[id], TCIOFLUSH) != 0) {
    __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Error when trying to flush write part\n");
  }

  __PO_HI_DEBUG_DEBUG ("[DRVMGR SERIAL] Initialization complete !\n");
}
