/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2020 OpenAADL
 */

#if (defined (__PO_HI_NEED_DRIVER_1553_RASTA))\n
/*
Code automatically generated by asn1scc tool
*/
#include <limits.h>
#include <string.h>
#include <math.h>


#include "1553.h"



void __po_hi_c_Node_Addr_T_Initialize(__po_hi_c_Node_Addr_T* pVal)
{
	(void)pVal;


	(*(pVal)) = 0;
}

flag __po_hi_c_Node_Addr_T_IsConstraintValid(const __po_hi_c_Node_Addr_T* pVal, int* pErrCode)
{
    flag ret = TRUE;
	(void)pVal;
	
    ret = ((*(pVal)) <= 31UL);
    *pErrCode = ret ? 0 :  ERR_NODE_ADDR_T; 

	return ret;
}



void __po_hi_c_Standard_T_Initialize(__po_hi_c_Standard_T* pVal)
{
	(void)pVal;


	(*(pVal)) = __po_hi_c_mil1553a;
}

flag __po_hi_c_Standard_T_IsConstraintValid(const __po_hi_c_Standard_T* pVal, int* pErrCode)
{
    flag ret = TRUE;
	(void)pVal;
	
    ret = ((((*(pVal)) == __po_hi_c_mil1553a)) || (((*(pVal)) == __po_hi_c_mil1553b)));
    *pErrCode = ret ? 0 :  ERR_STANDARD_T; 

	return ret;
}



void __po_hi_c_Mode_T_Initialize(__po_hi_c_Mode_T* pVal)
{
	(void)pVal;


	(*(pVal)) = __po_hi_c_controller;
}

flag __po_hi_c_Mode_T_IsConstraintValid(const __po_hi_c_Mode_T* pVal, int* pErrCode)
{
    flag ret = TRUE;
	(void)pVal;
	
    ret = ((((((*(pVal)) == __po_hi_c_controller)) || (((*(pVal)) == __po_hi_c_terminal)))) || (((*(pVal)) == __po_hi_c_monitor)));
    *pErrCode = ret ? 0 :  ERR_MODE_T; 

	return ret;
}



void __po_hi_c_Bus_T_Initialize(__po_hi_c_Bus_T* pVal)
{
	(void)pVal;


	(*(pVal)) = __po_hi_c_none;
}

flag __po_hi_c_Bus_T_IsConstraintValid(const __po_hi_c_Bus_T* pVal, int* pErrCode)
{
    flag ret = TRUE;
	(void)pVal;
	
    ret = ((((((((*(pVal)) == __po_hi_c_none)) || (((*(pVal)) == __po_hi_c_bus_a)))) || (((*(pVal)) == __po_hi_c_bus_b)))) || (((*(pVal)) == __po_hi_c_both)));
    *pErrCode = ret ? 0 :  ERR_BUS_T; 

	return ret;
}



void __po_hi_c_mil_1553_conf_t_devname_Initialize(__po_hi_c_mil_1553_conf_t_devname val)
{
	(void)val;


	memset(val, 0x0, 21);

}
void __po_hi_c_mil_1553_conf_t_Initialize(__po_hi_c_mil_1553_conf_t* pVal)
{
	(void)pVal;



	/*set devname */
	__po_hi_c_mil_1553_conf_t_devname_Initialize(pVal->devname);
	/*set standard */
	__po_hi_c_Standard_T_Initialize((&(pVal->standard)));
	/*set mode */
	__po_hi_c_Mode_T_Initialize((&(pVal->mode)));
	/*set bus */
	__po_hi_c_Bus_T_Initialize((&(pVal->bus)));
	/*set termaddr */
	__po_hi_c_Node_Addr_T_Initialize((&(pVal->termaddr)));
	/*set broadcast */
	pVal->broadcast = FALSE;
	/*set rxblock */
	pVal->exist.rxblock = 1;
	pVal->rxblock = FALSE;
	/*set txblock */
	pVal->exist.txblock = 1;
	pVal->txblock = FALSE;
}

flag __po_hi_c_mil_1553_conf_t_IsConstraintValid(const __po_hi_c_mil_1553_conf_t* pVal, int* pErrCode)
{
    flag ret = TRUE;
	(void)pVal;
	
    ret = ((1 <= strlen(pVal->devname)) && (strlen(pVal->devname) <= 20));
    *pErrCode = ret ? 0 :  ERR_MIL_1553_CONF_T_DEVNAME; 
    if (ret) {
        ret = (((pVal->standard == __po_hi_c_mil1553a)) || ((pVal->standard == __po_hi_c_mil1553b)));
        *pErrCode = ret ? 0 :  ERR_MIL_1553_CONF_T_STANDARD; 
        if (ret) {
            ret = (((((pVal->mode == __po_hi_c_controller)) || ((pVal->mode == __po_hi_c_terminal)))) || ((pVal->mode == __po_hi_c_monitor)));
            *pErrCode = ret ? 0 :  ERR_MIL_1553_CONF_T_MODE; 
            if (ret) {
                ret = (((((((pVal->bus == __po_hi_c_none)) || ((pVal->bus == __po_hi_c_bus_a)))) || ((pVal->bus == __po_hi_c_bus_b)))) || ((pVal->bus == __po_hi_c_both)));
                *pErrCode = ret ? 0 :  ERR_MIL_1553_CONF_T_BUS; 
                if (ret) {
                    ret = (pVal->termaddr <= 31UL);
                    *pErrCode = ret ? 0 :  ERR_MIL_1553_CONF_T_TERMADDR; 
                }
            }
        }
    }

	return ret;
}

\n#endif
