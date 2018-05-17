/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2016 ESA & ISAE.
 */

/*! \file po_hi_driver_rasta_serial.c
 *  \brief Driver that interface PolyORB-HI-C and the serial interface of RASTA boards using the RTEMS 4.8 driver.
 *
 *  This driver works ONLY with the RTEMS 4.8 version that was available on GAISLER website
 *  on April 2010. This version is available at:
 *    - http://download.tuxfamily.org/taste/tools/rtems-4.8-gaisler.tgz
 *  However, please note that it is no longer supported by GAISLER and contains
 *  other bugs (such as the serial driver for the LEON that does not work).
 */

#include <deployment.h>
/* Generated code header */

#ifdef __PO_HI_NEED_DRIVER_SERIAL_RASTA

#include <activity.h>
#include <marshallers.h>

#include <po_hi_debug.h>
#include <po_hi_transport.h>
#include <po_hi_gqueue.h>
#include <po_hi_messages.h>
#include <po_hi_returns.h>
#include <po_hi_utils.h>
#include <drivers/po_hi_rtems_utils.h>
#include <drivers/po_hi_driver_rasta_serial.h>
#include <drivers/po_hi_driver_rasta_common.h>

#include <drivers/po_hi_driver_serial_common.h>

#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <termios.h>
/* POSIX-style files */

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>
/* Rasta includes from GAISLER drivers */

#include <drivers/configuration/serial.h>

int po_hi_c_driver_rasta_serial_fd_read[__PO_HI_NB_DEVICES];
int po_hi_c_driver_rasta_serial_fd_write[__PO_HI_NB_DEVICES];

__po_hi_request_t    __po_hi_c_driver_serial_rasta_request;
__po_hi_msg_t        __po_hi_c_driver_serial_rasta_poller_msg;

/*!
 * \fn void __po_hi_c_driver_serial_rasta_poller (const __po_hi_device_id dev_id)
 * \brief Polling function for the RASTA.
 *
 * This function is the poller for the serial interface of the RASTA board.
 * It is supposed to be called by the underlying AADL code at a given period/rate.
 * The argument dev_id is the device_id handled by the device driver. By using
 * such an argument, we can use this function on a single node that uses several
 * driver instances (several serial interfaces connected to different serial buses).
 */

void __po_hi_c_driver_serial_rasta_poller (const __po_hi_device_id dev_id)
{
   int                  n;
   int                  ts;
   uint8_t*             ptr;

   ts = __PO_HI_MESSAGES_MAX_SIZE;
   ptr = &(__po_hi_c_driver_serial_rasta_poller_msg.content[0]);
   __po_hi_msg_reallocate (&__po_hi_c_driver_serial_rasta_poller_msg);
   while (ts > 0)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Poller waits for incoming message (%d bytes are required)!\n", ts);
      n = read (po_hi_c_driver_rasta_serial_fd_read[dev_id], ptr, ts); 

      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] read() %d returns %d!\n", po_hi_c_driver_rasta_serial_fd_read[dev_id], n);
      if (n == -1)
      {
         __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Cannot read on socket !\n");
         return;
      }
      else
      {
         ptr += n;
         ts -= n;
      }
   }

   __po_hi_c_driver_serial_rasta_poller_msg.length = __PO_HI_MESSAGES_MAX_SIZE;

   __po_hi_unmarshall_request (&__po_hi_c_driver_serial_rasta_request,
                               &__po_hi_c_driver_serial_rasta_poller_msg);

   if (__po_hi_c_driver_serial_rasta_request.port > __PO_HI_NB_PORTS)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Invalid port number (%d), will not deliver", __po_hi_c_driver_serial_rasta_request.port);
   }
   __po_hi_main_deliver (&__po_hi_c_driver_serial_rasta_request);
}
#ifdef RTEMS48
extern amba_confarea_type* __po_hi_driver_rasta_common_get_bus ();
#elif RTEMS411
extern struct ambapp_bus * __po_hi_driver_rasta_common_get_bus ();
#else
#error "o<"
#endif

void __po_hi_rasta_interrrupt_register(void *handler, int irqno, void *arg);

/*!
 * \fn void __po_hi_c_driver_serial_rasta_init (__po_hi_device_id id)
 * \brief Initialization function for the RASTA serial driver.
 *
 * This function  is used to initialize the device driver connected to the
 * serial interface to a RASTA board. It uses the configuration properties
 * from its associated configuration parameters (using the 
 * __po_hi_get_device_configuration function).
 */

void __po_hi_c_driver_serial_rasta_init (__po_hi_device_id id)
{
   uint32_t max_size;

   __po_hi_c_serial_conf_t* serialconf;

   __po_hi_c_driver_rasta_common_init ();

   serialconf = (__po_hi_c_serial_conf_t*)__po_hi_get_device_configuration (id);

   if (serialconf == NULL)
   {
      __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Cannot get the name of the device !\n");
      return;
   }

   __po_hi_transport_set_sending_func (id, __po_hi_c_driver_serial_rasta_sender);

    /* provide the spacewire driver with AMBA Plug&Play
     * info so that it can find the GRSPW cores.
     */

   __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Initialization starts !\n");

   po_hi_c_driver_rasta_serial_fd_write[id] = 
   po_hi_c_driver_rasta_serial_fd_read[id] = open (serialconf->devname, O_RDWR);
   /*
   po_hi_c_driver_rasta_serial_fd_write = open (serialconf->devname, O_WRONLY);
   */

   if (po_hi_c_driver_rasta_serial_fd_read[id] < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[RASTA SERIAL] Error while opening device %s for reading\n", serialconf->devname);
   }
   if (po_hi_c_driver_rasta_serial_fd_write[id] < 0)
   {
      __PO_HI_DEBUG_CRITICAL ("[RASTA SERIAL] Error while opening device %s for writing\n", serialconf->devname);
   }

   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Device opened for read (%s), fd=%d\n", serialconf->devname , po_hi_c_driver_rasta_serial_fd_read[id]);
   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Device opened for write (%s), fd=%d\n", serialconf->devname , po_hi_c_driver_rasta_serial_fd_write[id]);

   switch (__po_hi_c_driver_serial_common_get_speed (id))
   {
      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_19200:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_BAUDRATE, 19200);
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_write[id], APBUART_SET_BAUDRATE, 19200);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_38400:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_BAUDRATE, 38400);
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_write[id], APBUART_SET_BAUDRATE, 38400);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_57600:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_BAUDRATE, 57600);
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_write[id], APBUART_SET_BAUDRATE, 57600);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_115200:
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_BAUDRATE, 115200);
         __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_write[id], APBUART_SET_BAUDRATE, 115200);
         break;

      case __PO_HI_DRIVER_SERIAL_COMMON_SPEED_UNKNWON:
         __PO_HI_DEBUG_INFO ("[RASTA SERIAL] Unknwon speed for the serial line\n");
         break;
   }

   /*
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BLOCKING, APBUART_BLK_RX | APBUART_BLK_TX | APBUART_BLK_FLUSH);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd, APBUART_SET_BLOCKING, APBUART_BLK_FLUSH | APBUART_BLK_RX);
  */

   max_size = 1024;
#ifdef __PO_HI_MESSAGES_MAX_SIZE
   max_size = 4 * __PO_HI_MESSAGES_MAX_SIZE;
#endif
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_BLOCKING, APBUART_BLK_FLUSH | APBUART_BLK_TX );
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_TXFIFO_LEN, max_size);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_RXFIFO_LEN, max_size);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_SET_ASCII_MODE, 0); /* Make \n go \n\r or \r\n */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_CLR_STATS, 0);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(po_hi_c_driver_rasta_serial_fd_read[id], APBUART_START, 0);


  if (tcflush (po_hi_c_driver_rasta_serial_fd_read[id], TCIOFLUSH) != 0)
  {
     __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Error when trying to flush read part\n");
  }

  if (tcflush (po_hi_c_driver_rasta_serial_fd_write[id], TCIOFLUSH) != 0)
  {
     __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Error when trying to flush write part\n");
  }

  __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Initialization complete !\n");
}


__po_hi_msg_t           __po_hi_c_driver_serial_rasta_sender_msg;

/*!
 * \fn int __po_hi_c_driver_serial_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
 * \brief Function related to the RASTA serial driver - sender function.
 *
 * This function implements the sender function to send bytes through the serial line using
 * the RASTA device. 
 * There are the description of the arguments used by the function:
 *   - task_id: task that actually sends the data (emitter/producer task)
 *   - port   : (global) port that contains the data
 * It returns the following possible values :
 *   - __PO_HI_UNAVAILABLE : the driver does not handle the device connected to argument port.
 *   - __PO_HI_SUCCESS     : either no value was available to be sent or the function
 *                           send the message successfully over the network.
 */
int __po_hi_c_driver_serial_rasta_sender (const __po_hi_task_id task_id, const __po_hi_port_t port)
{
   int                     n;
   int                     ts;
   __po_hi_local_port_t    local_port;
   __po_hi_request_t*      request;
   __po_hi_port_t          destination_port;
   __po_hi_device_id       dev_id;

   dev_id = __po_hi_get_device_from_port (port);

   if (dev_id == invalid_device_id)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Invalid device id for sending\n");
      return __PO_HI_UNAVAILABLE;
   }

   local_port = __po_hi_get_local_port_from_global_port (port);

   request = __po_hi_gqueue_get_most_recent_value (task_id, local_port);

   if (request->port == -1)
   {
      __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Send output task %d, port %d (local_port=%d): no value to send\n", task_id, port, local_port);
      return __PO_HI_SUCCESS;
   }

   destination_port     = __po_hi_gqueue_get_destination (task_id, local_port, 0);

   __po_hi_msg_reallocate (&__po_hi_c_driver_serial_rasta_sender_msg);

   request->port = destination_port;
   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] Destination port= %d, send through device %d (fd=%d)\n", destination_port, dev_id, po_hi_c_driver_rasta_serial_fd_write[dev_id]);

   __po_hi_marshall_request (request, &__po_hi_c_driver_serial_rasta_sender_msg);

   n = write (po_hi_c_driver_rasta_serial_fd_write[dev_id], &__po_hi_c_driver_serial_rasta_sender_msg, __PO_HI_MESSAGES_MAX_SIZE);

   __PO_HI_DEBUG_DEBUG ("[RASTA SERIAL] write() returns %d\n", n);

   request->port = __PO_HI_GQUEUE_INVALID_PORT;

   return 1;
}

#endif
