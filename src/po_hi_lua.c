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
#include <po_hi_time.h>


#ifdef __PO_HI_USE_LUA
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

int __po_hi_lua_load (__po_hi_lua_context_t* context, const char* filename)
{
   if (context == NULL)
   {
      return __PO_HI_INVALID;
   }

   if (filename == NULL)
   {
      return __PO_HI_INVALID;
   }

#ifdef __PO_HI_USE_LUA
   context->state = lua_open();

   luaL_openlibs (context->state);

   lua_register (context->state, "time_wait", __po_hi_lua_time_wait);

   if (luaL_dofile (context->state,filename) != 0)
   {
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

#endif


