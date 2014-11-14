/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_GENERIC_KEYBOARD

#include <stdio.h>
#include <stdlib.h>
#include <curses.h>
#include <stdio.h>    /* Standard input/output definitions */
#include <stdlib.h> 
#include <stdint.h>   /* Standard types */
#include <string.h>   /* String function definitions */
#include <unistd.h>   /* UNIX standard function definitions */
#include <fcntl.h>    /* File control definitions */
#include <errno.h>    /* Error number definitions */
#include <termios.h>  /* POSIX terminal control definitions */
#include <sys/ioctl.h>
#include <getopt.h>
#include <po_hi_debug.h>


void __po_hi_driver_generic_keyboard_poller (const __po_hi_device_id dev_id, int* key_pressed)
{
   (void) dev_id;
   int key;
   __DEBUGMSG ("POLL THE KEYBOARD\n");
   key = getch ();
   if (key != ERR)
   {
      *key_pressed = key;
   }
   else
   {
      *key_pressed = 0;
   }
}

void __po_hi_driver_generic_keyboard_init (__po_hi_device_id id)
{
   WINDOW* win = initscr();
   keypad (stdscr, TRUE);
   noecho ();
   nodelay (win, TRUE);

   __DEBUGMSG ("INIT KEYBOARD\n");
}

#endif
