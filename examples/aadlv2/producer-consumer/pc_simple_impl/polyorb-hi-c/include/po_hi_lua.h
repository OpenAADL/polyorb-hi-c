/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://taste.tuxfamily.org/wiki
 *
 * Copyright (C) 2012-2014 ESA & ISAE.
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

#define __PO_HI_LUA_FUNCTION_NAME_MAX_SIZE 100

#ifdef __PO_HI_USE_LUA
#include <lua/lua.h>
#include <lua/lualib.h>
#include <lua/lauxlib.h>

typedef struct
{
   lua_State*  state;
   int         nb_args;
   char        function_name[__PO_HI_LUA_FUNCTION_NAME_MAX_SIZE];
}__po_hi_lua_context_t;

/*!
 * \fn __po_hi_lua_load (__po_hi_lua_context_t*, const char*);
 * \brief load a lua script and initialize a lua context
 *
 * this function takes the following arguments:
 *   - 1st arg: a lua context that will contain the execution of the script
 *   - 2nd arg: the name of the script
 *
 *  it returns the potential values:
 *    - __po_hi_failure: fails to load the script
 *    - __po_hi_invalid: invalid lua context
 *    - __po_hi_success: successfully load the script
 */
int __po_hi_lua_load (__po_hi_lua_context_t*, const char*);

/*!
 * \fn __po_hi_lua_load (__po_hi_lua_context_t*, const char*);
 * \brief load a lua script and initialize a lua context
 *
 * this function takes the following arguments:
 *   - 1st arg: a lua context that will contain the execution of the script
 *   - 2nd arg: the name of the script
 *
 *  it returns the potential values:
 *    - __po_hi_failure: fails to load the script
 *    - __po_hi_invalid: invalid lua context
 *    - __po_hi_success: successfully load the script
 */
int __po_hi_lua_load_str (__po_hi_lua_context_t*, const char*);

/*!
 * \fn __po_hi_lua_init_function_call (__po_hi_lua_context_t*, const char*);
 * \brief Initialize a function-call within a LUA execution context
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that contains the function to be called.
 *   - 2nd arg: The name of the function to be called.
 *
 *  It returns the potential values:
 *    - __PO_HI_INVALID: invalid LUA context or invalid function name
 *    - __PO_HI_SUCCESS: successful operation
 */
int __po_hi_lua_init_function_call (__po_hi_lua_context_t*, const char*);

/*!
 * \fn __po_hi_lua_perform_function_call (__po_hi_lua_context_t*);
 * \brief Perform a function call previously initalized.
 *
 * In fact, this function really performs the function calls. When
 * you want to make a call to a function from a LUA script, you have
 * to perform the following function calls:
 * __po_hi_lua_load                    : load the script
 * __po_hi_lua_init_function_call      : prepare the function call
 * __po_hi_lua_push_XXXX               : push the arguments of the function
 * __po_hi_lua_perform_function_call   : finally make the effective call
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that contains the function to be called and was
 *              used during the previous __po_hi_lua_init_function_call call
 *
 *  It returns the potential values:
 *    - __PO_HI_ERROR:   error while calling the LUA function
 *    - __PO_HI_SUCCESS: successful operation
 */

int __po_hi_lua_perform_function_call (__po_hi_lua_context_t*);

/*!
 * \fn __po_hi_lua_push_number (__po_hi_lua_context_t*, int);
 * \brief Push a number value on the stack before calling a LUA function.
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The value to put on the stack
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to put the value on the stack
 *    - __PO_HI_INVALID: invalid LUA context
 *    - __PO_HI_SUCCESS: successfully push the value on the LUA stack
 */
int __po_hi_lua_push_number (__po_hi_lua_context_t*, int);

/*!
 * \fn __po_hi_lua_push_boolean (__po_hi_lua_context_t*, int);
 * \brief Push a boolean value on the stack before calling a LUA function.
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The value to put on the stack
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to put the value on the stack
 *    - __PO_HI_INVALID: invalid LUA context
 *    - __PO_HI_SUCCESS: successfully push the value on the LUA stack
 */
int __po_hi_lua_push_boolean (__po_hi_lua_context_t*, int);

/*!
 * \fn __po_hi_lua_push_string (__po_hi_lua_context_t*, char*);
 * \brief Push a string value on the stack before calling a LUA function.
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The value to put on the stack (a string)
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to put the value on the stack
 *    - __PO_HI_INVALID: invalid LUA context
 *    - __PO_HI_SUCCESS: successfully push the value on the LUA stack
 */

int __po_hi_lua_push_string (__po_hi_lua_context_t*, char*);

/*!
 * \fn __po_hi_lua_get_boolean (__po_hi_lua_context_t*, char*, int*);
 * \brief Get a number value from a global variable from a LUA script
 *        and inject it in C code.
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The global variable name in the LUA script
 *   - 2rd arg: Pointer to the integer value to be filled.
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to convert the variable to a number
 *                       or non-existent variable
 *    - __PO_HI_SUCCESS: successfully convert the variable from LUA to C
 *
 */
int __po_hi_lua_get_number (__po_hi_lua_context_t*, char*, int*);

/*!
 * \fn __po_hi_lua_get_boolean (__po_hi_lua_context_t*, char*, int*);
 * \brief Get a boolean value from the global variable from a LUA script
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The global variable name in the LUA script
 *   - 2rd arg: Pointer to the boolean/integer value to be filled.
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to convert the variable to a boolean
 *                       or non-existent variable
 *    - __PO_HI_SUCCESS: successfully convert the variable from LUA to C
 *
 */
int __po_hi_lua_get_boolean (__po_hi_lua_context_t*, char*, int*);

/*!
 * \fn __po_hi_lua_get_string (__po_hi_lua_context_t*, char*, char*);
 * \brief Get a string value from the global variable from a LUA script
 *
 * This function takes the following arguments:
 *   - 1st arg: A LUA context that executed a script
 *   - 2nd arg: The global variable name in the LUA script
 *   - 2rd arg: Pointer to the string value to be filled.
 *
 *  It returns the potential values:
 *    - __PO_HI_FAILURE: fails to convert the variable to a string
 *                       or non-existent variable
 *    - __PO_HI_SUCCESS: successfully convert the variable from LUA to C
 *
 */
int __po_hi_lua_get_string (__po_hi_lua_context_t*, char*, char*);



#else
#include <po_hi_debug.h>
typedef int __po_hi_lua_context_t;
#endif /* ifdef __PO_HI_USE_LUA */

#endif /* __PO_HI_LUA_H__ */
