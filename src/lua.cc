#include "lua.h"


static const struct luaL_Reg lnacho_instructions_lib_f [] = {
    {"new", lnacho_instructions_new},
    {NULL, NULL}
};


static const struct luaL_Reg lnacho_instructions_lib_m [] = {
    {"from_queso_file", lnacho_instructions_from_queso_file},
    {"from_json_file", lnacho_instructions_from_json_file},
    {"slice_forward", lnacho_instructions_slice_forward},
    {"slice_backward", lnacho_instructions_slice_backward},
    {"smtlib2", lnacho_instructions_smtlib2},
    {"instructions", lnacho_instructions_instructions},
    {"concretize", lnacho_instructions_concretize},
    {"ssa_variable", lnacho_instructions_ssa_variable},
    {"__gc", lnacho_instructions_gc},
    {NULL, NULL}
};


LUALIB_API int luaopen_lnacho (lua_State * L)
{
    luaL_newmetatable(L, "lnacho.instructions_t");
    lua_pushstring   (L, "__index");
    lua_pushvalue    (L, -2);
    lua_settable     (L, -3);
    luaL_register    (L, NULL, lnacho_instructions_lib_m);
    luaL_register    (L, "instructions_t", lnacho_instructions_lib_f);
    
    return 2;
}


Instructions * lnacho_instructions_check (lua_State * L, int position)
{
    void * userdata = luaL_checkudata(L, position, "lnacho.instructions_t");
    luaL_argcheck(L, userdata != NULL, position, "lnacho.instructions_t expected");
    return *((Instructions **) userdata);
}


int lnacho_instructions_new (lua_State * L)
{
    Instructions ** instructions = (Instructions **) lua_newuserdata(L, sizeof(Instructions *));
    *instructions = new Instructions();

    luaL_getmetatable(L, "lnacho.instructions_t");
    lua_setmetatable(L, -2);

    return 1;
}


int lnacho_instructions_from_queso_file (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    const char * filename = luaL_checkstring(L, 2);

    lua_pop(L, 2);

    bool result = instructions->from_queso_file(filename);
    if (result) 
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 2);

    return 1;
}

int lnacho_instructions_from_json_file (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    const char * filename = luaL_checkstring(L, 2);

    lua_pop(L, 2);

    bool result = instructions->from_json_file(filename);
    if (result) 
        lua_pushboolean(L, 1);
    else
        lua_pushboolean(L, 2);

    return 1;
}

int lnacho_instructions_slice_forward (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    const char * variable_name = luaL_checkstring(L, 2);
    unsigned int variable_count = luaL_checkinteger(L, 3);

    lua_pop(L, 3);

    Variable * variable = new Variable(variable_name, 0);
    variable->s_count(variable_count);

    lnacho_instructions_new(L);
    Instructions * result = lnacho_instructions_check(L, 1);
    result->s_copy_instructions(instructions->slice_forward(*variable));

    delete variable;

    return 1;
}

int lnacho_instructions_slice_backward (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    const char * variable_name = luaL_checkstring(L, 2);
    unsigned int variable_count = luaL_checkinteger(L, 3);

    lua_pop(L, 3);

    Variable * variable = new Variable(variable_name, 0);
    variable->s_count(variable_count);

    lnacho_instructions_new(L);
    Instructions * result = lnacho_instructions_check(L, 1);
    result->s_copy_instructions(instructions->slice_backward(*variable));

    delete variable;

    return 1;
}

int lnacho_instructions_smtlib2 (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);

    std::string smtlib2 = instructions->smtlib2();

    lua_pop(L, 1);
    lua_pushstring(L, smtlib2.c_str());

    return 1;
}

int lnacho_instructions_instructions (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);

    lua_pop(L, 1);

    lua_newtable(L);

    int i = 1;

    std::list <Instruction *> da_ins_list = instructions->g_instructions();
    std::list <Instruction *> :: iterator it;
    for (it = da_ins_list.begin(); it != da_ins_list.end(); it++) {
        lua_pushinteger(L, i++);
        push_instruction_table(L, *it);
        lua_settable(L, -3);
    }

    return 1;
}

int lnacho_instructions_concretize (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);

    lua_pop(L, 1);

    instructions->concretize();

    return 0;
}

int lnacho_instructions_ssa_variable (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    const char * variable_name = luaL_checkstring(L, 2);

    lua_pop(L, 2);

    instructions->ssa_var(variable_name);

    return 0;
}

int lnacho_instructions_gc (lua_State * L)
{
    Instructions * instructions = lnacho_instructions_check(L, 1);
    delete instructions;
    lua_pop(L, 1);
    return 0;
}


void push_variable_table (lua_State * L, Variable & variable)
{
    lua_newtable(L);

    lua_pushstring(L, "bits");
    lua_pushinteger(L, variable.g_bits());
    lua_settable(L, -3);

    lua_pushstring(L, "count");
    lua_pushinteger(L, variable.g_count());
    lua_settable(L, -3);

    switch (variable.g_type()) {
    case VARIABLE_VAR :
        lua_pushstring(L, "type");
        lua_pushstring(L, "variable");
        lua_settable(L, -3);

        lua_pushstring(L, "name");
        lua_pushstring(L, variable.g_name().c_str());
        lua_settable(L, -3);
        break;

    case VARIABLE_CONST :
        lua_pushstring(L, "type");
        lua_pushstring(L, "constant");
        lua_settable(L, -3);

        lua_pushstring(L, "lval");
        lua_pushinteger(L, variable.g_lval());
        lua_settable(L, -3);

        lua_pushstring(L, "lvalhex");
        char tmp[64];
        snprintf(tmp, 64, "%016llx", (unsigned long long) variable.g_lval());
        lua_pushstring(L, tmp);
        lua_settable(L, -3);
        break;

    case VARIABLE_ARRAY :
        lua_pushstring(L, "type");
        lua_pushstring(L, "array");
        lua_settable(L, -3);

        lua_pushstring(L, "name");
        lua_pushstring(L, variable.g_name().c_str());
        lua_settable(L, -3);

        lua_pushstring(L, "addresses");
        lua_pushinteger(L, variable.g_addresses());
        lua_settable(L, -3);
    }
}

void push_instruction_table (lua_State * L, Instruction * instruction)
{
    lua_newtable(L);

    lua_pushstring(L, "opcode");
    if (InstructionComment * ins = dynamic_cast <InstructionComment *> (instruction)) {
        lua_pushstring(L, "comment");
        lua_settable(L, -3);

        lua_pushstring(L, "comment");
        lua_pushstring(L, ins->g_comment().c_str());
        lua_settable(L, -3);
    }
    else if (InstructionAssign * ins = dynamic_cast <InstructionAssign *> (instruction)) {
        lua_pushstring(L, "assign");
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);

        lua_pushstring(L, "src");
        push_variable_table(L, ins->g_src());
        lua_settable(L, -3);
    }
    else if (InstructionStore * ins = dynamic_cast <InstructionStore *> (instruction)) {
        lua_pushstring(L, "store");
        lua_settable(L, -3);

        lua_pushstring(L, "dstmem");
        push_variable_table(L, ins->g_dstmem());
        lua_settable(L, -3);

        lua_pushstring(L, "srcmem");
        push_variable_table(L, ins->g_srcmem());
        lua_settable(L, -3);

        lua_pushstring(L, "address");
        push_variable_table(L, ins->g_address());
        lua_settable(L, -3);

        lua_pushstring(L, "value");
        push_variable_table(L, ins->g_value());
        lua_settable(L, -3);
    }
    else if (InstructionLoad * ins = dynamic_cast<InstructionLoad *> (instruction)) {
        lua_pushstring(L, "load");
        lua_settable(L, -3);

        lua_pushstring(L, "mem");
        push_variable_table(L, ins->g_mem());
        lua_settable(L, -3);

        lua_pushstring(L, "address");
        push_variable_table(L, ins->g_address());
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);
    }
    else if (InstructionIte * ins = dynamic_cast<InstructionIte *> (instruction)) {
        lua_pushstring(L, "ite");
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);

        lua_pushstring(L, "condition");
        push_variable_table(L, ins->g_condition());
        lua_settable(L, -3);

        lua_pushstring(L, "t");
        push_variable_table(L, ins->g_t());
        lua_settable(L, -3);

        lua_pushstring(L, "e");
        push_variable_table(L, ins->g_e());
        lua_settable(L, -3);
    }
    else if (InstructionSignExtend * ins = dynamic_cast<InstructionSignExtend *> (instruction)) {
        lua_pushstring(L, "signextend");
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);

        lua_pushstring(L, "src");
        push_variable_table(L, ins->g_src());
        lua_settable(L, -3);
    }
    else if (InstructionArithmetic * ins = dynamic_cast<InstructionArithmetic *> (instruction)) {
        lua_pushstring(L, ins->g_opcode().c_str());
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);

        lua_pushstring(L, "lhs");
        push_variable_table(L, ins->g_lhs());
        lua_settable(L, -3);

        lua_pushstring(L, "rhs");
        push_variable_table(L, ins->g_rhs());
        lua_settable(L, -3);
    }
    else if (InstructionCmp * ins = dynamic_cast<InstructionCmp *> (instruction)) {
        lua_pushstring(L, ins->g_opcode().c_str());
        lua_settable(L, -3);

        lua_pushstring(L, "dst");
        push_variable_table(L, ins->g_dst());
        lua_settable(L, -3);

        lua_pushstring(L, "lhs");
        push_variable_table(L, ins->g_lhs());
        lua_settable(L, -3);

        lua_pushstring(L, "rhs");
        push_variable_table(L, ins->g_rhs());
        lua_settable(L, -3);
    }


}