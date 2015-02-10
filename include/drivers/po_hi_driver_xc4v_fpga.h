/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#include <deployment.h>

#ifdef __PO_HI_NEED_DRIVER_XC4V_FPGA

int __po_hi_driver_xc4v_fpga_initialize ();
/*
 * Return 1 if success, 0 otherwise
 */

unsigned __po_hi_driver_xc4v_fpga_read_register (unsigned offset);
/*
 * Read a register in the FPGA at offset position.
 * Returns the value of the register.
 */

void __po_hi_driver_xc4v_fpga_write_register (unsigned offset, unsigned value);
/*
 * Write the register at offset with the value value in parameters.
 */

#endif /* __PO_HI_NEED_DRIVER_XC4V_FPGA */
