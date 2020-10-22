/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2018-2019 ESA & ISAE, 2019-2020 OpenAADL
 */

#include <stdbool.h>
#include <stdlib.h>

#include <po_hi_debug.h>

extern void system_init (void); /* defined as part of RTEMS config.c */
extern void drvmgr_print_topo(void);

void __po_hi_c_driver_drvmgr_init (void) {

  static bool init_done = false;

  if (!init_done) {
    init_done = true;

    /* Initialize Driver manager and Networking, in config.c */
    system_init();

    /* Print device topology */
    drvmgr_print_topo();

    __PO_HI_DEBUG_DEBUG ("[DRVMGR] Initialization done \n");

  } else {
    __PO_HI_DEBUG_DEBUG ("[DRVMGR] Initialization already done \n");
  }

}
