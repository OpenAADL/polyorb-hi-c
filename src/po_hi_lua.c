/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
 */

#include <po_hi_lua.h>
#include <po_hi_debug.h>
#include <po_hi_time.h>
#include <po_hi_types.h>


#ifdef __PO_HI_USE_LUA

#include <string.h>
int __po_hi_lua_time_wait (lua_State* state)
{
   __po_hi_time_t now;
   __po_hi_time_t delay;
   __po_hi_time_t deadline;

   int msec;

   msec = lua_tonumber (state, 1);

   __po_hi_get_time (&now);
   __po_hi_milliseconds (&delay, msec);
   __po_hi_add_times (&deadline, &now, &delay);
   __po_hi_delay_until (&deadline);
   return 0;
}

int __po_hi_lua_time_delay_until (lua_State* state)
{
   __po_hi_time_t delay;
   int sec;
   int nsec;

   sec = lua_tonumber (state, 1);
   nsec = lua_tonumber (state, 2);

   delay.sec   = sec;
   delay.nsec  = nsec;

   __po_hi_delay_until (&delay);

   return 0;
}


int __po_hi_lua_time_get (lua_State* state)
{
   __po_hi_time_t now;

   __po_hi_get_time (&now);

   __PO_HI_DEBUG_INFO ("[LUA] time_get sec  =%llu\n", now.sec);
   __PO_HI_DEBUG_INFO ("[LUA] time_get nsec =%llu\n", now.nsec);

   lua_pushnumber (state, now.sec);
   lua_pushnumber (state, now.nsec);

   return 2;
}

int __po_hi_lua_init (__po_hi_lua_context_t* context)
{
   if (context == NULL)
   {
      return __PO_HI_INVALID;
   }
#ifdef __PO_HI_USE_LUA
   context->state = luaL_newstate();

   luaL_openlibs (context->state);

   lua_register (context->state, "time_wait", __po_hi_lua_time_wait);
   lua_register (context->state, "time_get", __po_hi_lua_time_get);
   lua_register (context->state, "time_delay_until", __po_hi_lua_time_delay_until);
#endif 

   return __PO_HI_SUCCESS;

}

int __po_hi_lua_load_str (__po_hi_lua_context_t* context, const char* str)
{
   if (str == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (__po_hi_lua_init (context) != __PO_HI_SUCCESS)
   {
      return __PO_HI_INVALID;
   }

#ifdef __PO_HI_USE_LUA
   if (luaL_dostring (context->state,str) != 0)
   {
      __PO_HI_DEBUG_DEBUG ("[LUA] Fail to load LUA str %s !", str);
      return __PO_HI_INVALID;
   }
#endif 
   return __PO_HI_SUCCESS;
}


int __po_hi_lua_load (__po_hi_lua_context_t* context, const char* filename)
{
   if (filename == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (__po_hi_lua_init (context) != __PO_HI_SUCCESS)
   {
      return __PO_HI_INVALID;
   }

#ifdef __PO_HI_USE_LUA
   if (luaL_dofile (context->state,filename) != 0)
   {
      __PO_HI_DEBUG_DEBUG ("[LUA] Fail to load LUA file %s !", filename);
      return __PO_HI_INVALID;
   }
#endif 
   return __PO_HI_SUCCESS;
}

int __po_hi_lua_init_function_call (__po_hi_lua_context_t* ctx, const char* fctname)
{
   int len; 

   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (fctname == NULL)
   {
      return __PO_HI_INVALID;
   }

   len = strlen (fctname);

   if ( len >= __PO_HI_LUA_FUNCTION_NAME_MAX_SIZE)
   {
      return __PO_HI_INVALID;
   }

   memset (ctx->function_name, '\0', __PO_HI_LUA_FUNCTION_NAME_MAX_SIZE);

   memcpy (ctx->function_name, fctname, len);

   ctx->nb_args = 0;

   lua_getglobal(ctx->state, fctname);

   if (!lua_isfunction(ctx->state,-1))
   {
      __PO_HI_DEBUG_DEBUG ("[LUA] Function %s does not exists !", fctname);

      lua_pop(ctx->state,1);

      return __PO_HI_INVALID;
   }

   return __PO_HI_SUCCESS;
}

int __po_hi_lua_perform_function_call (__po_hi_lua_context_t* ctx)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   lua_call (ctx->state, ctx->nb_args, 0);
   return __PO_HI_SUCCESS;
}


int __po_hi_lua_push_number (__po_hi_lua_context_t* ctx, int val)
{
   ctx->nb_args = ctx->nb_args + 1;
   lua_pushnumber (ctx->state, val);

   return __PO_HI_SUCCESS;
}


int __po_hi_lua_push_boolean (__po_hi_lua_context_t* ctx, int val)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   ctx->nb_args = ctx->nb_args + 1;

   lua_pushboolean (ctx->state, val);

   return __PO_HI_SUCCESS;
}


int __po_hi_lua_push_string (__po_hi_lua_context_t* ctx, char* val)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   ctx->nb_args = ctx->nb_args + 1;

   lua_pushstring (ctx->state, val);
   return __PO_HI_SUCCESS;
}


int __po_hi_lua_get_number (__po_hi_lua_context_t* ctx, char* varname, int* val)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   lua_settop (ctx->state,0);
   lua_getglobal (ctx->state,varname);
   *val = lua_tonumber (ctx->state,1);
   lua_pop (ctx->state,1);
   return __PO_HI_SUCCESS;
}


int __po_hi_lua_get_boolean (__po_hi_lua_context_t* ctx, char* varname, int* val)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   return __PO_HI_SUCCESS;
}


int __po_hi_lua_get_string (__po_hi_lua_context_t* ctx, char* varname, char* val)
{
   if (ctx == NULL)
   {
      return __PO_HI_INVALID;
   }

   return __PO_HI_SUCCESS;
}

#else

/*
 * Stub functions when LUA is not enabled
 */

int __po_hi_lua_load(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_load_str(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_init_function_call(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_perform_function_call(arg1)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_push_number(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_push_boolean(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_push_string(arg1,arg2)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_get_number(arg1,arg2,arg3)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_get_boolean(arg1,arg2,arg3)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

int __po_hi_lua_get_string(arg1,arg2,arg3)
{
   __PO_HI_DEBUG_INFO ("[%s:%d] LUA not implemented\n", __FILE__, __LINE__); 
   return __PO_HI_UNAVAILABLE;
}

#endif
