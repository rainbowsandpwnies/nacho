#ifndef lua_HEADER
#define lua_HEADER

#include <lua5.1/lua.h>
#include <lua5.1/lualib.h>
#include <lua5.1/lauxlib.h>

#include "instructions.h"


LUALIB_API int luaopen_lnacho (lua_State * L);


Instructions * lnacho_instructions_check (lua_State * L, int position);

int lnacho_instructions_new (lua_State * L);

int lnacho_instructions_from_queso_file (lua_State * L);
int lnacho_instructions_from_json_file  (lua_State * L);
int lnacho_instructions_slice_forward   (lua_State * L);
int lnacho_instructions_slice_backward  (lua_State * L);
int lnacho_instructions_smtlib2         (lua_State * L);
int lnacho_instructions_instructions    (lua_State * L);
int lnacho_instructions_concretize      (lua_State * L);
int lnacho_instructions_ssa_variable    (lua_State * L);

int lnacho_instructions_gc  (lua_State * L);

void push_variable_table    (lua_State * L, Variable & variable);
void push_instruction_table (lua_State * L, Instruction * instruction);

#endif