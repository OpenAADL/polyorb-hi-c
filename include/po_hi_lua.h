/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.assert-online.net/taste
 *
 * Copyright (C) 2012, European Space Agency (ESA)
 */


#ifndef __PO_HI_LUA_H__
#define __PO_HI_LUA_H__

#include <po_hi_config.h>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <po_hi_returns.h>

#ifdef HAVE_LIBLUA5_1
#define __PO_HI_USE_LUA
#else
#undef __PO_HI_USE_LUA
#endif

#ifdef __PO_HI_USE_LUA
#include <lua5.1/lua.h>
#include <lua5.1/lualib.h>
#include <lua5.1/lauxlib.h>
#endif

int __po_hi_lua_load (const char*, const char*);


#endif

