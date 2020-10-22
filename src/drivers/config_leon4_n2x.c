/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

#include <bsp/gr_leon4_n2x.h>

// Things are always moving around in RTEMS - adapt.
// The latest RTEMS (2019/07) has restructured Leon/AMBA
// headers under grlib. Detect this by a combination of checks,
// that depends on the fact that our custom cross build in TASTE
// enabled Ada (which Gaisler's RCC doesn't).
#if ((__RTEMS_ADA__ != 0) && (((__RTEMS_MAJOR__ << 8) | (__RTEMS_MINOR__ << 0)) >= 0x0500))
   #include <grlib/ambapp_bus.h>
#else
   #include <drvmgr/ambapp_bus.h>
#endif

/* GR-CPCI-LEON4-N2X boards configuration example. Note that this is
 * optional, we only override defaults. If default are ok, nothing
 * is need to be done.
 */

/*** Driver resources for GR-LEON4-N2X 0 AMBA PnP bus ***/
struct drvmgr_bus_res gr_leon4_n2x0_res =
{
        .next = NULL,
        .resource = {
                DRVMGR_RES_EMPTY
        },
};

/* Use GPTIMER core 4 (not present in most systems) as a high
 * resoulution timer */
struct drvmgr_key leon4_n2x1_gptimer1[] =
{
        {"prescaler", DRVMGR_KT_INT, {(unsigned int)4}},
        DRVMGR_KEY_EMPTY
};


/*** Driver resources for GR-LEON4-N2X 1 AMBA PnP bus ***/
struct drvmgr_bus_res gr_leon4_n2x1_res =
{
        .next = NULL,
        .resource = {
                {DRIVER_AMBAPP_GAISLER_GPTIMER_ID, 0, NULL}, /*disable GPT[0]*/
                {DRIVER_AMBAPP_GAISLER_GPTIMER_ID, 1, &leon4_n2x1_gptimer1[0]},
                DRVMGR_RES_EMPTY
        },
};

/* Tell GR-CPCI-LEON4-N2X driver about the bus resources.
 * Resources for two GR-CPCI-LEON4-N2X board are available.
 * AMBAPP->PCI->GR-CPCI-LEON4-N2X->AMBAPP bus resources
 *
 * The resources will be used by the drivers for the
 * cores found on the GR-CPCI-LEON4-N2X->AMBAPP bus.
 *
 * The "weak defaults" are overriden here.
 */
struct drvmgr_bus_res *gr_leon4_n2x_resources[] =
{
        &gr_leon4_n2x0_res,		/* GR-LEON4-N2X board 1 resources */
        &gr_leon4_n2x1_res,		/* GR-LEON4-N2X board 2 resources */
        NULL,				/* End of table */
};
