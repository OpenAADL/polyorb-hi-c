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

#ifdef POSIX
#include <string.h>
#endif

#ifdef HAVE_LIBLUA5_1
#define __PO_HI_USE_LUA
#else
#undef __PO_HI_USE_LUA
#endif

#ifdef __PO_HI_USE_LUA
#include <lua5.1/lua.h>
#include <lua5.1/lualib.h>
#include <lua5.1/lauxlib.h>

#define __PO_HI_LUA_FUNCTION_NAME_MAX_SIZE 100

typedef struct
{
   lua_State*  state;
   int         nb_args;
   char        function_name[__PO_HI_LUA_FUNCTION_NAME_MAX_SIZE];
}__po_hi_lua_context_t;
#else
typedef int __po_hi_lua_context_t;
#endif

int __po_hi_lua_load (__po_hi_lua_context_t*, const char*);

int __po_hi_lua_init_function_call (__po_hi_lua_context_t*, const char*);

int __po_hi_lua_perform_function_call (__po_hi_lua_context_t*);

int __po_hi_lua_push_number (__po_hi_lua_context_t*, int);

int __po_hi_lua_push_boolean (__po_hi_lua_context_t*, int);

int __po_hi_lua_push_string (__po_hi_lua_context_t*, char*);

int __po_hi_lua_get_number (__po_hi_lua_context_t*, char*, int*);

int __po_hi_lua_get_boolean (__po_hi_lua_context_t*, char*, int*);

int __po_hi_lua_get_string (__po_hi_lua_context_t*, char*, char*);



#endif

