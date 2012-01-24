/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.assert-online.net/taste
 *
 * Copyright (C) 2012, European Space Agency (ESA)
 */

#include <po_hi_lua.h>

int __po_hi_lua_load (const char* filename, const char* functionname)
{
#ifdef __PO_HI_USE_LUA
   lua_State * state;
   state = lua_open();
   luaL_openlibs(state);
   if (luaL_dofile (state,filename) != 0)
   {
      return __PO_HI_INVALID;
   }
#endif 
   return __PO_HI_SUCCESS;
}
