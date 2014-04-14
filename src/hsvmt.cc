#include "hsvmt.h"

#include <cstdio>
#include <iostream>


Hsvmt :: Hsvmt ()
{
    input_byte_count = 0;
}


void Hsvmt :: setmem (uint8_t * memory, size_t size, uint64_t address)
{
    Variable mem = Variable("mem", 16, 8);

    for (size_t i = 0; i < size; i++) {
        if (address + i > 65536)
            break;
        instructions.append(new InstructionStore(mem, Variable(16, address + i), Variable(8, memory[i]), address + i));
    }
}


Variable Hsvmt :: reg_to_var (uint8_t reg)
{
    switch (reg) {
    case REG_0  : return Variable("r0", 16);
    case REG_1  : return Variable("r1", 16);
    case REG_2  : return Variable("r2", 16);
    case REG_3  : return Variable("r3", 16);
    case REG_4  : return Variable("r4", 16);
    case REG_5  : return Variable("r5", 16);
    case REG_6  : return Variable("r6", 16);
    case REG_7  : return Variable("r7", 16);
    case REG_BP : return Variable("rbp", 16);
    case REG_SP : return Variable("rsp", 16);
    case REG_IP : return Variable("rip", 16);
    }
    return Variable("INVALID", 0);
}


Variable Hsvmt :: lval_to_var (uint16_t lval)
{
    return Variable(16, (uint16_t ) ((lval >> 8) | (lval << 8)));
}


void Hsvmt :: store16 (const Variable & mem, const Variable & address, const Variable & value, uint64_t trace_address)
{
    Variable storel8 = Variable("storel8", 8);
    Variable storeh8 = Variable("storeh8", 8);
    Variable storeh16 = Variable("storeh16", 16);
    Variable address2 = Variable("address2", 16);

    instructions.append(new InstructionShr(storeh16, value, Variable(16, 8)));
    instructions.append(new InstructionAssign(storeh8, storeh16));
    instructions.append(new InstructionStore(mem, address, storeh8, trace_address));

    instructions.append(new InstructionAssign(storel8, value));
    instructions.append(new InstructionAdd(address2, address, Variable(16, 1)));
    instructions.append(new InstructionStore(mem, address2, storel8, trace_address + 1));
}


Variable Hsvmt :: load16 (const Variable & mem, const Variable & address, uint64_t trace_address)
{
    Variable loadl8 = Variable("loadl8", 8);
    Variable loadh8 = Variable("loadh8", 8);
    Variable loadl16 = Variable("loadh16", 16);
    Variable loadh16 = Variable("loadh16", 16);
    Variable loadh162 = Variable("loadh162", 16);
    Variable result = Variable("load16", 16);
    Variable address2 = Variable("address2", 16);

    instructions.append(new InstructionLoad(mem, address, loadh8, trace_address));
    instructions.append(new InstructionAdd(address2, address, Variable(16, 1)));
    instructions.append(new InstructionLoad(mem, address2, loadl8, trace_address));

    instructions.append(new InstructionAssign(loadl16, loadl8));
    instructions.append(new InstructionAssign(loadh16, loadh8));
    instructions.append(new InstructionShl(loadh162, loadh16, Variable(16, 8)));
    instructions.append(new InstructionOr(result, loadh162, loadl16));

    return result;
}


bool Hsvmt :: translate (uint8_t * data, uint32_t size, uint64_t address, uint64_t trace_address)
{
    ins = (struct _instruction *) data;
    
    Variable lval = lval_to_var(ins->lval);
    
    Variable oper0 = reg_to_var(ins->operand_0);
    Variable oper1 = reg_to_var(ins->operand_1);
    Variable oper2 = reg_to_var(ins->operand_2);
    Variable mem = Variable("mem", 16, 8);

    switch (ins->opcode) {
    case OP_ADD : instructions.append(new InstructionAdd(oper0, oper1, oper2)); break;
    case OP_SUB : instructions.append(new InstructionSub(oper0, oper1, oper2)); break;
    case OP_MUL : instructions.append(new InstructionMul(oper0, oper1, oper2)); break;
    case OP_DIV : instructions.append(new InstructionUdiv(oper0, oper1, oper2)); break;
    case OP_MOD : instructions.append(new InstructionUmod(oper0, oper1, oper2)); break;
    case OP_AND : instructions.append(new InstructionAnd(oper0, oper1, oper2)); break;
    case OP_OR  : instructions.append(new InstructionOr(oper0, oper1, oper2)); break;
    case OP_XOR : instructions.append(new InstructionXor(oper0, oper1, oper2)); break;
    case OP_ADDLVAL : instructions.append(new InstructionAdd(oper0, oper0, lval)); break;
    case OP_SUBLVAL : instructions.append(new InstructionSub(oper0, oper0, lval)); break;
    case OP_MULLVAL : instructions.append(new InstructionMul(oper0, oper0, lval)); break;
    case OP_DIVLVAL : instructions.append(new InstructionUdiv(oper0, oper0, lval)); break;
    case OP_MODLVAL : instructions.append(new InstructionUmod(oper0, oper0, lval)); break;
    case OP_ANDLVAL : instructions.append(new InstructionAnd(oper0, oper0, lval)); break;
    case OP_ORLVAL  : instructions.append(new InstructionOr(oper0, oper0, lval)); break;
    case OP_XORLVAL : instructions.append(new InstructionXor(oper0, oper0, lval));
    case OP_JMP :
    {
        Variable rip = Variable("rip", 16);
        instructions.append(new InstructionAdd(rip, rip, lval));
        break;
    }
    case OP_JE :
        instructions.append(new InstructionCmpEq(Variable("tmp", 1), Variable("flags", 16), Variable(16, 0)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_JNE :
        instructions.append(new InstructionCmpEq(Variable("tmp", 1), Variable("flags", 16), Variable(16, 0)));
        instructions.append(new InstructionXor(Variable("tmp", 1), Variable("tmp", 1), Variable((uint64_t) 1, 1)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_JL :
        instructions.append(new InstructionCmpLts(Variable("tmp", 1), Variable("flags", 16), Variable(16, 0)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_JLE :
        instructions.append(new InstructionCmpLes(Variable("tmp", 1), Variable("flags", 16), Variable(16, 0)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_JG :
        instructions.append(new InstructionCmpLts(Variable("tmp", 1), Variable(16, 0), Variable("flags", 16)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_JGE :
        instructions.append(new InstructionCmpLes(Variable("tmp", 1), Variable(16, 0), Variable("flags", 16)));
        instructions.append(new InstructionAdd(Variable("tmp2", 16), Variable("rip", 16), lval));
        instructions.append(new InstructionIte(Variable("rip", 16), Variable("tmp", 1), Variable("tmp2", 16), Variable("rip", 16)));
        break;
    case OP_CALL :
        instructions.append(new InstructionSub(Variable("rsp", 16), Variable("rsp", 16), Variable(16, 2)));
        store16(mem, Variable("rsp", 16), Variable("rip", 16), trace_address);
        instructions.append(new InstructionAdd(Variable("rsp", 16), Variable("rsp", 16), lval));
        break;
    case OP_RET :
    {
        Variable tmp = load16(mem, Variable("rsp", 16), trace_address);
        instructions.append(new InstructionAssign(Variable("rsp", 16), tmp));
        instructions.append(new InstructionAdd(Variable("rsp", 16), Variable("rsp", 16), Variable(16, 2)));
        break;
    }
    case OP_LOAD :
    {
        Variable tmp = load16(mem, lval, trace_address);
        instructions.append(new InstructionAssign(oper0, tmp));
        break;
    }
    case OP_LOADR :
    {
        Variable tmp = load16(mem, oper1, trace_address);
        instructions.append(new InstructionAssign(oper0, tmp));
        break;
    }
    case OP_LOADB :
    {
        Variable tmp8 = Variable("tmp", 8);
        instructions.append(new InstructionLoad(mem, lval, tmp8, trace_address));
        instructions.append(new InstructionAssign(oper0, tmp8));
        break;
    }
    case OP_LOADBR :
    {
        Variable tmp8 = Variable("tmp", 8);
        instructions.append(new InstructionLoad(mem, oper1, tmp8, trace_address));
        instructions.append(new InstructionAssign(oper0, tmp8));
        break;
    }
    case OP_STOR :
        store16(mem, lval, oper0, trace_address);
        break;
    case OP_STORR :
        store16(mem, oper0, oper1, trace_address);
        break;
    case OP_STORB :
    {
        Variable tmp8 = Variable("tmp", 8);
        instructions.append(new InstructionAssign(tmp8, oper0));
        instructions.append(new InstructionStore(mem, lval, tmp8, trace_address));
        break;
    }
    case OP_STORBR :
    {
        Variable tmp8 = Variable("tmp", 8);
        instructions.append(new InstructionAssign(tmp8, oper1));
        instructions.append(new InstructionStore(mem, oper0, tmp8, trace_address));
        break;
    }
    case OP_IN :
    {
        char input_name [64];
        snprintf(input_name, 64, "in%d", input_byte_count++);
        Variable in = Variable(input_name, 8);
        instructions.append(new InstructionAssign(oper0, in));
        break;
    }
    case OP_OUT :
    {
        Variable out = Variable("out", 8);
        instructions.append(new InstructionAssign(out, oper0));
        break;
    }
    case OP_PUSH :
        instructions.append(new InstructionSub(Variable("rsp", 16), Variable("rsp", 16), Variable(16, 2)));
        store16(mem, Variable("rsp", 16), oper0, trace_address);
        break;
    case OP_PUSHLVAL :
        instructions.append(new InstructionSub(Variable("rsp", 16), Variable("rsp", 16), Variable(16, 2)));
        store16(mem, Variable("rsp", 16), lval, trace_address);
        break;
    case OP_POP :
    {
        Variable tmp = Variable("tmp", 16);
        tmp = load16(mem, Variable("rsp", 16), trace_address);
        instructions.append(new InstructionAdd(Variable("rsp", 16), Variable("rsp", 16), Variable(16, 2)));
        instructions.append(new InstructionAssign(oper0, tmp));
        break;
    }
    case OP_MOV :
        instructions.append(new InstructionAssign(oper0, oper1));
        break;
    case OP_MOVLVAL :
        instructions.append(new InstructionAssign(oper0, lval));
        break;
    case OP_CMP :
    {
        Variable flags = Variable("flags", 16);
        instructions.append(new InstructionSub(flags, oper0, oper1));
        break;
    }
    case OP_CMPLVAL :
    {
        Variable flags = Variable("flags", 16);
        instructions.append(new InstructionSub(flags, oper0, lval));
        break;
    }
    default :
        return false;
    }

    return true;
}