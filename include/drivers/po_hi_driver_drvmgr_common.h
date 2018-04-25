#ifndef __PO_HI_DRIVER_DRVMGR_COMMON__
#define __PO_HI_DRIVER_DRVMGR_COMMON__

/** Initializes RTEMS drvmgr sub-system
 *
 * This is necessary prior using any drivers using this manager.
 *
 * Note: applies mostly to SPARC-based bsps, e.g. leon3, gr740, n2x, ..
 */
void __po_hi_c_driver_drvmgr_init (void);

#endif
