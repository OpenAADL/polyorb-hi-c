/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2010-2014 ESA & ISAE.
 */

#ifdef __PO_HI_USE_GPROF

#include <po_hi_debug.h>
#include <drivers/po_hi_rtems_utils.h>

#include <pci.h>
#include <rasta.h>
#include <apbuart_rasta.h>



#define CONFIG_OS_PROFILE_OVER_SERIAL 1
#define SERIAL_VERBOSE_MODE 1

/*
 * Histogram counters are unsigned shorts (according to the kernel).
 */
#define	HISTCOUNTER	unsigned short

/*
 * Fraction of text space to allocate for histogram counters here, 1/2
 */
#define	HISTFRACTION_LOG2   (1)
#define	HISTFRACTION        (1 << HISTFRACTION_LOG2)

/*
 * Fraction of text space to allocate for from hash buckets.
 * The value of HASHFRACTION is based on the minimum number of bytes
 * of separation between two subroutine call points in the object code.
 * Given MIN_SUBR_SEPARATION bytes of separation the value of
 * HASHFRACTION is calculated as:
 *
 * 	HASHFRACTION = MIN_SUBR_SEPARATION / (2 * sizeof(short) - 1);
 *
 * For the VAX,
 *	the shortest two call sequence is:
 * 		calls	$0,(r0)
 *		calls	$0,(r0)
 * 	which is separated by only three bytes, thus HASHFRACTION is 
 *	calculated as:
 *		HASHFRACTION = 3 / (2 * 2 - 1) = 1
 *
 * For the m68k,
 *	the shortest two call sequence is:
 * 		jsr	a0
 *		jsr	a0
 * 	which is separated by only four bytes, thus HASHFRACTION is 
 *	calculated as:
 *		HASHFRACTION = 4 / (2 * 2 - 1) = 1
 *
 * For all RISC machines
 *	the shortest two call sequence is 2 32-bit instructions,
 * 	which is separated by only four bytes, thus HASHFRACTION is 
 *	calculated as:
 *		HASHFRACTION = 4 / (2 * 2 - 1) = 1
 *
 * For the i386,
 *	the shortest two call sequence is:
 * 		call	%eax
 *		call	%eax
 * 	which is separated by only two bytes, thus HASHFRACTION is 
 *	calculated as:
 *		HASHFRACTION = 2 / (2 * 2 - 1) = 0
 *	So on the i386 we use a HASHFRACTION of 1 instead and it can fail
 *	to determine that two call sites are different.  But since all
 *	the call site address in gprof(1) is currently used for is
 *	to determine which routine was doing the calling it works for now.
 *
 * Note that the division above rounds down, thus if MIN_SUBR_FRACTION
 * is less than three, this algorithm will not work!
 */
#define	HASHFRACTION	1

/*
 * percent of text space to allocate for tostructs with a minimum.
 */
#define ARCDENSITY	4
#define MINARCS		50

#ifndef ASSEMBLER
/*
 * The tostruct is used internal to the monitor library routines to implement
 * the recording of calls via mcount().
 */
struct tostruct {
    char		*selfpc;
    long		count;
    unsigned short	link;
    unsigned short	order;
};

/*
 * The phdr (profile header) structure is what appears at the beginning of a
 * mon.out (cc(1) -p) and gmon.out (cc(1) -pg) file and describes the histogram
 * counters.  The histogram counters are unsigned shorts which follow after the
 * header for ncnt - sizeof(struct phdr) bytes.
 */
struct phdr {
    char	*lpc; 	/* low program counter */
    char	*hpc; 	/* high program counter */
    int		ncnt;	/* number of bytes of histogram counters minius
                       sizeof(struct phdr) that follow */
};

/*
 * In a gmon.out (cc(1) -pg) file what follows the above histogram counters are
 * the raw arcs.  A raw arc contains pointers to the calling site, the called
 * site and a count.  These repeat in the gmon.out file after the histogram
 * counters to the end of the file.
 */
struct rawarc {
    unsigned long	raw_frompc;
    unsigned long	raw_selfpc;
    unsigned long	raw_count;
};

/*
 * In order to support more information than in the original mon.out and
 * gmon.out files there is an alternate gmon.out file format.  The alternate
 * gmon.out file format starts with a magic number then separates the
 * information with gmon_data structs.
 */
#define GMON_MAGIC 0xbeefbabe
struct gmon_data {
    unsigned long type; /* constant for type of data following this struct */
    unsigned long size; /* size in bytes of the data following this struct */
};

/*
 * The GMONTYPE_SAMPLES gmon_data.type is for the histogram counters described
 * above and has a struct phdr followed by the counters.
 */
#define GMONTYPE_SAMPLES	1
/*
 * The GMONTYPE_RAWARCS gmon_data.type is for the raw arcs described above.
 */
#define GMONTYPE_RAWARCS	2
/*
 * The GMONTYPE_ARCS_ORDERS gmon_data.type is for the raw arcs with a call
 * order field.  The order is the order is a sequence number for the order each
 * call site was executed.  Raw_order values start at 1 not zero.  Other than
 * the raw_order field this is the same information as in the struct rawarc.
 */
#define GMONTYPE_ARCS_ORDERS	3
struct rawarc_order {
    unsigned long	raw_frompc;
    unsigned long	raw_selfpc;
    unsigned long	raw_count;
    unsigned long	raw_order;
};
/*
 * The GMONTYPE_RLD_STATE gmon_data.type is for the rld_load()'ed state of the
 * program.
 * The informations starts with an unsigned long with the count of states:
 *	rld_nloaded_states
 * Then each state follows in the file.  The state is made up of 
 *	header_addr (where rld loaded this set of objects)
 *	nobjectfiles (the number of objects in this set)
 *		offsets into the string table (one for each object in the set)
 *	nbytes of string table
 *		the file name strings null terminated.
 */
#define GMONTYPE_RLD_STATE	4
/*
 * The GMONTYPE_DYLD_STATE gmon_data.type is for the dynamic link editor state
 * of the program.
 * The informations starts with an unsigned long with the count of states:
 *      image_count
 * Then each state follows in the file.  The state is made up of 
 *      image_header (the address where dyld loaded this image)
 *      vmaddr_slide (the amount dyld slid this image from it's vmaddress)
 *      name (the file name dyld loaded this image from)
 */
#define GMONTYPE_DYLD_STATE     5
#endif /* !ASSEMBLER */

/*
 * general rounding functions.
 */
#define ROUNDDOWN(x,y)	(((x)/(y))*(y))
#define ROUNDUP(x,y)	((((x)+(y)-1)/(y))*(y))

/**
 *  \file   gmon.c
 *  \brief  This file implements the gprof stub on the LEON2/3 over RTEMS.
 *
 *  The file implements the mcoung function responsible for recording the
 *  call-graph table.
 *  It also implements the functionality of the profil() function (see man(2)
 *  profil) by replacing the clock isr and wrapping the real Clock_isr() RTEMS
 *  function.
 *
 *  \author  Aitor Viana Sanchez (avs), Aitor.Viana.Sanchez@esa.int
 *
 *  \internal
 *    Created:  05/17/2010
 *   Revision:  $Id: gmon.c 1.4 05/17/2010 avs Exp $
 *   Compiler:  gcc/g++
 *    Company:  European Space Agency (ESA-ESTEC)
 *  Copyright:  Copyright (c) 2010, Aitor Viana Sanchez
 *
 *  This source code is released for free distribution under the terms of the
 *  GNU General Public License as published by the Free Software Foundation.
 * =====================================================================================
 */

/*-
 * Copyright (c) 1991, 1998 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. [rescinded 22 July 1999]
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

static char sccsid[] = "@(#)gmon.c	1.0 (E.S.A) 10/05/2010";

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>

#include <rtems.h>
#include <bsp.h>

void _mcount() __attribute__((weak, alias("mcount")));

/*  These variables are defined in the linkcmd linker script and point to the
 *  start and end of the text area
 */
extern unsigned int _endtext, text_start;
extern int initialize_serial();
extern void end_serial ();
extern void write_serial(uint8_t vector[] , unsigned int dim);

/*
 *	froms is actually a bunch of unsigned shorts indexing tos
 */
static int		profiling = 3;
static long		tolimit = 0;
static unsigned long	s_textsize = 0;

static unsigned short	*froms;
static struct tostruct	*tos = 0;
static char		*s_lowpc = 0;
static char		*s_highpc = 0;

static int	ssiz;
static int	s_profil_sz = 0;
static char	*sbuf = 0;
static char *s_profil = 0;

#define	MSG "No space for profiling buffer(s)\n"

#define SAVE_L1( _pc_ )  \
    do{ \
        asm volatile( "mov %%l1, %0" : "=r" (_pc_) : "0" (_pc_) );    \
    }while(0)

static void moncontrol( int mode );
static rtems_isr profile_clock_isr(rtems_vector_number vector);

static void moncontrol( int mode )
{
    if (mode) {
        /* start */
        s_profil = sbuf + sizeof(struct phdr);
        s_profil_sz = ssiz - sizeof(struct phdr);
        profiling = 0;
    } else {
        /* stop */
        s_profil = 0;
        s_profil_sz = 0;
        profiling = 3;
    }
}

static void _mcleanup()
{
    int			fromindex;
    int			endfrom;
    char		*frompc;
    int			toindex;
    struct rawarc	rawarc;
    int ret = -1;

    moncontrol(0);
#if (CONFIG_OS_PROFILE_OVER_SERIAL == 1)
    ret = initialize_serial();
    if( ret >= 0 )
    {
        write_serial( (uint8_t*)sbuf , (unsigned int)ssiz );
    }
#endif

//    fprintf( stderr , "[mcleanup] sbuf 0x%x ssiz %d\n" , (unsigned int)sbuf , (unsigned int)ssiz );
    endfrom = s_textsize / (HASHFRACTION * sizeof(*froms));
    for ( fromindex = 0 ; fromindex < endfrom ; fromindex++ ) {
        if ( froms[fromindex] == 0 ) {
            continue;
        }
        frompc = s_lowpc + (fromindex * HASHFRACTION * sizeof(*froms));
        for (toindex=froms[fromindex]; toindex!=0; toindex=tos[toindex].link) 
        {
           /*
            fprintf( stderr ,
                    "[mcleanup] frompc 0x%x selfpc 0x%x count %d\n" ,
                    (unsigned int)frompc , 
                    (unsigned int)tos[toindex].selfpc , 
                    (unsigned int)tos[toindex].count );
                    */
            rawarc.raw_frompc = (unsigned long) frompc;
            rawarc.raw_selfpc = (unsigned long) tos[toindex].selfpc;
            rawarc.raw_count = tos[toindex].count;
            if( ret >= 0 )
            {
#if (CONFIG_OS_PROFILE_OVER_SERIAL == 1)
            write_serial( (uint8_t*)&rawarc , (unsigned int)sizeof(rawarc));
#endif
            }
        }
    }
#if (CONFIG_OS_PROFILE_OVER_SERIAL == 1)
    end_serial ();
#endif

}

void monstartup(char *lowpc, char *highpc)
{
    int			monsize;
    char		*buffer;

    printf("%s\n", sccsid);
    /*
     *	round lowpc and highpc to multiples of the density we're using
     *	so the rest of the scaling (here and in gprof) stays in ints.
     */
    lowpc = (char *)
        ROUNDDOWN((unsigned) lowpc, HISTFRACTION*sizeof(HISTCOUNTER));
    s_lowpc = lowpc;
    highpc = (char *)
        ROUNDUP((unsigned) highpc, HISTFRACTION*sizeof(HISTCOUNTER));
    s_highpc = highpc;
    s_textsize = highpc - lowpc;
    monsize = (s_textsize / HISTFRACTION) + sizeof(struct phdr);
    buffer = (char*)malloc( monsize );
    if ( buffer == (char *) -1 ) 
    {
        printf("%s\n", MSG);
        return;
    }
    froms = (unsigned short *) malloc( s_textsize / HASHFRACTION );
    if ( froms == (unsigned short *) -1 ) 
    {
        printf("%s\n", MSG);
        froms = 0;
        return;
    }
    tolimit = s_textsize * ARCDENSITY / 100;
    if ( tolimit < MINARCS ) {
        tolimit = MINARCS;
    } else if ( tolimit > 65534 ) {
        tolimit = 65534;
    }
    tos = (struct tostruct *) malloc( tolimit * sizeof( struct tostruct ) );
    if ( tos == (struct tostruct *) -1 ) 
    {
        printf("%s\n", MSG);
        froms = 0;
        tos = 0;
        return;
    }
    tos[0].link = 0;
    sbuf = buffer;
    bzero( buffer, sizeof(buffer) );
    ssiz = monsize;
    ( (struct phdr *) sbuf ) -> lpc = lowpc;
    ( (struct phdr *) sbuf ) -> hpc = highpc;
    ( (struct phdr *) sbuf ) -> ncnt = ssiz;
    monsize -= sizeof(struct phdr);
    if ( monsize <= 0 )
        return;

    printf("PC histrogram scale = %d\n", HISTFRACTION);

    /*  Register the new clock driver   */
    set_vector( profile_clock_isr, 0x18, 1 );
    atexit( _mcleanup );
    moncontrol(1);
}

void mcount()
{
    register char			*selfpc;
    register unsigned short		*frompcindex;
    register struct tostruct	*top;
    register struct tostruct	*prevtop;
    register long			toindex;
    static int first_call = 1;

    if( first_call )
    {
        monstartup((char*)&text_start, (char*)&_endtext);
        first_call = 0;
    }

    /*
     *	find the return address for mcount,
     *	and the return address for mcount's caller.
     */

    /* selfpc = pc pushed by mcount call.
       This identifies the function that was just entered.  */
    selfpc = (void *) __builtin_return_address (0);
    /* frompcindex = pc in preceding frame.
       This identifies the caller of the function just entered.  */
    frompcindex = (void *) __builtin_return_address (1);

    /*
     *	check that we are profiling
     *	and that we aren't recursively invoked.
     */
    if (profiling) {
        goto out;
    }
    profiling++;
    /*
     *	check that frompcindex is a reasonable pc value.
     *	for example:	signal catchers get called from the stack,
     *			not from text space.  too bad.
     */
    frompcindex = (unsigned short *) ((long) frompcindex - (long) s_lowpc);
    if ((unsigned long) frompcindex > s_textsize) {
        goto done;
    }
    frompcindex =
        &froms[((long) frompcindex) / (HASHFRACTION * sizeof(*froms))];
    toindex = *frompcindex;
    if (toindex == 0) {
        /*
         *	first time traversing this arc
         */
        toindex = ++tos[0].link;
        if (toindex >= tolimit) {
            goto overflow;
        }
        *frompcindex = toindex;
        top = &tos[toindex];
        top->selfpc = selfpc;
        top->count = 1;
        top->link = 0;
        goto done;
    }
    top = &tos[toindex];
    if (top->selfpc == selfpc) {
        /*
         *	arc at front of chain; usual case.
         */
        top->count++;
        goto done;
    }
    /*
     *	have to go looking down chain for it.
     *	top points to what we are looking at,
     *	prevtop points to previous top.
     *	we know it is not at the head of the chain.
     */
    for (; /* goto done */; ) {
        if (top->link == 0) {
            /*
             *	top is end of the chain and none of the chain
             *	had top->selfpc == selfpc.
             *	so we allocate a new tostruct
             *	and link it to the head of the chain.
             */
            toindex = ++tos[0].link;
            if (toindex >= tolimit) {
                goto overflow;
            }
            top = &tos[toindex];
            top->selfpc = selfpc;
            top->count = 1;
            top->link = *frompcindex;
            *frompcindex = toindex;
            goto done;
        }
        /*
         *	otherwise, check the next arc on the chain.
         */
        prevtop = top;
        top = &tos[top->link];
        if (top->selfpc == selfpc) {
            /*
             *	there it is.
             *	increment its count
             *	move it to the head of the chain.
             */
            top->count++;
            toindex = prevtop->link;
            prevtop->link = top->link;
            top->link = *frompcindex;
            *frompcindex = toindex;
            goto done;
        }

    }
done:
    profiling--;
    /* and fall through */
out:
    return;		/* normal return restores saved registers */

overflow:
    profiling++; /* halt further profiling */
    fprintf( stderr, "%s: tos overflow", __func__ );
    goto out;
}

extern rtems_status_code __real_Clock_isr();
extern rtems_status_code Clock_isr();

static uint32_t pc = 0;
rtems_isr __wrap_Clock_isr()
{
    if( s_profil && s_profil_sz )
    {
       /*   This identifies the function that was just entered.  */
//        SAVE_L1(pc);
        if( pc )
        {
            pc -= (int)s_lowpc;
            pc = (pc >> HISTFRACTION_LOG2);
            if( pc < s_profil_sz )  s_profil[pc]++;
        }
    }
    pc = 0;

    __real_Clock_isr();
    
}

static rtems_isr profile_clock_isr(rtems_vector_number vector)
{
    SAVE_L1(pc);
    Clock_isr(vector);
    
}

#if (CONFIG_OS_PROFILE_OVER_SERIAL == 1)

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <termios.h>
#include <stdio.h>
#include <errno.h>
#include <sys/systm.h>

#define SERIAL_VERBOSE_MODE   1
#define BAUDRATE B57600

/******************************************************
 *         Private global variables declaration
 ******************************************************/

/**
 * the serial connection file descriptor
 **/
static int serialFD = -1;


/******************************************************
 *            Function implementation
 ******************************************************/

int initialize_serial()
{
   __DEBUGMSG ("[RASTA SERIAL] Init\n");
   init_pci();
   __DEBUGMSG ("[RASTA SERIAL] Initializing RASTA ...\n");
  if  ( rasta_register() ){
    __DEBUGMSG(" ERROR !\n");
    return -1;
  }
   __DEBUGMSG(" OK !\n");



  serialFD = open( "/dev/apburasta0" , O_RDWR);
  if( serialFD < 0 )
  {
#if(SERIAL_VERBOSE_MODE == 1)
    printk("can't open new device! error = %d\n" , serialFD);
#endif
    return -1;
  }
  
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_SET_BAUDRATE, 38400); /* stream mode */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_SET_BLOCKING, APBUART_BLK_RX | APBUART_BLK_TX | APBUART_BLK_FLUSH);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_SET_TXFIFO_LEN, 64);  /* Transmitt buffer 64 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_SET_RXFIFO_LEN, 256); /* Receive buffer 256 chars */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_SET_ASCII_MODE, 0); /* Make \n go \n\r or \r\n */
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_CLR_STATS, 0);
  __PO_HI_DRIVERS_RTEMS_UTILS_IOCTL(serialFD, APBUART_START, 0);
  if (tcflush (serialFD, TCIOFLUSH) != 0)
  {
     __DEBUGMSG("[GPROF] Error when trying to flush\n");
  }


#if(SERIAL_VERBOSE_MODE == 1)
    printk("Serial init done (using file descriptor %d)\n" , serialFD);
#endif
  
  return 0;
}

void write_serial(uint8_t vector[] , unsigned int dim)
{
   write(serialFD , vector , dim);
   /*
   for (i = 0 ; i < dim ; i++)
   {
      write(serialFD , &vector[i] , 1);
   }
   */

   if (tcflush (serialFD, TCIOFLUSH) != 0)
   {
      __DEBUGMSG("[GPROF] Error when trying to flush serial port\n");
   }
}

void end_serial ()
{
      __DEBUGMSG("[GPROF] Analysis results sent\n");
}

#endif /* TIMELINE_USE_SERIAL_CABLE */



#endif
