/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

/* Note, this file is from RCC1.3rc4 sample directory.
 *
 * Any modification there should be carefully weighted.
 */

// Things are always moving around in RTEMS - adapt.
// The latest RTEMS (2019/07) has restructured Leon/AMBA
// headers under grlib. Detect this by a combination of checks,
// that depends on the fact that our custom cross build in TASTE
// enabled Ada (which Gaisler's RCC doesn't).
#if ((__RTEMS_ADA__ != 0) && (((__RTEMS_MAJOR__ << 8) | (__RTEMS_MINOR__ << 0)) >= 0x0500))
#include <grlib/ambapp_bus_grlib.h>
#include <grlib/ambapp_bus.h>
#include <grlib/ambapp_ids.h>
#else
#include <drvmgr/ambapp_bus_grlib.h>
#include <drvmgr/ambapp_bus.h>
#include <ambapp_ids.h>
#endif

/* B1553RT driver configuration (optional) */
struct drvmgr_key grlib_drv_res_b1553rt0[] =
{
#ifdef SET_B1553RT_FREQ
        {"coreFreq", DRVMGR_KT_INT, {(unsigned int)SET_B1553RT_FREQ}},
#endif
        DRVMGR_KEY_EMPTY
};

/* GRPCI driver configuration (optional) */
struct drvmgr_key grlib_drv_res_grpci0[] =
{
        {"byteTwisting", DRVMGR_KT_INT, {(unsigned int)1}},
        DRVMGR_KEY_EMPTY
};

/* GRPCI2 driver configuration (optional) */
struct drvmgr_key grlib_drv_res_grpci2_0[] =
{
#if 0
        {"INTA#", DRVMGR_KT_INT, {(unsigned int)3}},
        {"INTB#", DRVMGR_KT_INT, {(unsigned int)3}},
        {"INTC#", DRVMGR_KT_INT, {(unsigned int)3}},
        {"INTD#", DRVMGR_KT_INT, {(unsigned int)3}},
#endif
        DRVMGR_KEY_EMPTY
};

/* GRGPIO0 driver configuration (optional) */
struct drvmgr_key grlib_drv_res_grgpio0[] =
{
#if 0
        {"nBits", DRVMGR_KT_INT, {(unsigned int)24}},
#endif
        {"int1", DRVMGR_KT_INT,  {(unsigned int)1}},
        {"ptr2", DRVMGR_KT_POINTER,  {(unsigned int)0x23334445}},
        {"str3", DRVMGR_KT_STRING,  {(unsigned int)"STRING_ValUe"}},
        DRVMGR_KEY_EMPTY
};

/* GRGPIO1 driver configuration (optional) */
struct drvmgr_key grlib_drv_res_grgpio1[] =
{
        {"nBits", DRVMGR_KT_INT, {(unsigned int)8}},
        DRVMGR_KEY_EMPTY
};

/* GRGPIO1 driver configuration (optional) */
struct drvmgr_key grlib_drv_res_spictrl0[] =
{
#ifdef SPICTRL_SLV_SEL_FUNC
        {"slvSelFunc", DRVMGR_KT_POINTER, {(unsigned int)SPICTRL_SLV_SEL_FUNC}},
#endif
        DRVMGR_KEY_EMPTY
};

/* If RTEMS_DRVMGR_STARTUP is defined we override the "weak defaults" that
 * is defined by the LEON3 BSP.
 */
struct drvmgr_bus_res grlib_drv_resources =
{
        .next = NULL,
        .resource = {
        {DRIVER_AMBAPP_GAISLER_GRPCI2_ID, 0, &grlib_drv_res_grpci2_0[0]},
#ifdef LITTLE_ENDIAN_PCI_SYSTEM
        /* this configuration option enables PCI byte-twisting which is
         * required for little-endian PCI systems such as for UT699 and
         * the GR-LEON4-ITX board.
         */
        {DRIVER_AMBAPP_GAISLER_GRPCI_ID, 0, &grlib_drv_res_grpci0[0]},
#endif
/*
        {DRIVER_AMBAPP_GAISLER_B1553RT_ID, 0, &grlib_drv_res_b1553rt0[0]},
        {DRIVER_AMBAPP_GAISLER_SPICTRL_ID, 0, &grlib_drv_res_spictrl0[0]},
*/
        {DRIVER_AMBAPP_GAISLER_GRGPIO_ID, 0, &grlib_drv_res_grgpio0[0]},
        DRVMGR_RES_EMPTY
        }
};

#ifndef RTEMS_DRVMGR_STARTUP
struct grlib_config grlib_bus_config =
{
        &ambapp_plb,		/* AMBAPP bus setup */
        &grlib_drv_resources,	/* Driver configuration */
};
#endif

/* LEON3 specific system init */
void system_init2(void)
{
#ifndef RTEMS_DRVMGR_STARTUP
        /* Register GRLIB root bus */
        ambapp_grlib_root_register(&grlib_bus_config);
#endif
}
