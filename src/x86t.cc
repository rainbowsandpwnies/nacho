#include "x86t.h"

#include <iostream>
#include <sstream>

#define DEBUG

X86t :: X86t ()
{
    cs_open(CS_ARCH_X86, CS_MODE_64, &cshandle);
    cs_option(cshandle, CS_OPT_DETAIL, CS_OPT_ON);
    cs_option(cshandle, CS_OPT_SYNTAX, CS_OPT_SYNTAX_INTEL);
    tmp_counter = 0;
}

X86t :: ~X86t ()
{
    clear_instructions();
    cs_close(&cshandle);
}


void X86t :: clear_instructions ()
{
    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++)
        delete *it;
    instructions.clear();
}


Variable X86t :: gen_tmp_var (int bits)
{
    std::stringstream ss;
    ss << "tmp" << tmp_counter++;
    return Variable(ss.str(), bits);
}


uint16_t X86t :: size ()
{
    return insn_size;
}


std::list <Instruction *> X86t :: translate (uint8_t * data, uint32_t size, uint64_t address)
{
    clear_instructions();
    insn_size = 0;

    if (cs_disasm_ex(cshandle, data, size, address, 1, &insn_array) == 0)
        return instructions;

    insn = &(insn_array[0]);
    x86 = &(insn->detail->x86);
    insn_size = insn->size;

    #ifdef DEBUG
    std::cout << "; " << insn->mnemonic << " " << insn->op_str << std::endl;
    #endif

    switch (insn->id) {
        case X86_INS_ADD : ins_add (); break;
        default :
            #ifdef DEBUG2
            std::cout << "unhandled instruction (" << insn->id << ") " << insn->mnemonic << " " 
                      << insn->op_str << "\n";
            #endif
            break;
    }

    return instructions;
}


Variable X86t :: get_operand (int operand)
{
    if (x86->operands[operand].type == X86_OP_REG) {

        #ifdef DEBUG3
        std::cout << "get_operand X86_OP_REG" << std::endl;
        #endif

        switch (x86->operands[operand].reg) {
            case X86_REG_AL :
            {
                Variable al("al", 8);
                instructions.push_back(new InstructionAssign(al, Variable("rax", 64)));
                return al;
            }
            case X86_REG_BL :
            {
                Variable bl("bl", 8);
                instructions.push_back(new InstructionAssign(bl, Variable("rbx", 64)));
                return bl;
            }
            case X86_REG_CL :
            {
                Variable cl("cl", 8);
                instructions.push_back(new InstructionAssign(cl, Variable("rcx", 64)));
                return cl;
            }
            case X86_REG_DL :
            {
                Variable dl("dl", 8);
                instructions.push_back(new InstructionAssign(dl, Variable("rdx", 64)));
                return dl;
            }
            case X86_REG_RAX : return Variable("rax", 64); break;
            case X86_REG_RBX : return Variable("rbx", 64); break;
            case X86_REG_RCX : return Variable("rcx", 64); break;
            case X86_REG_RDX : return Variable("rdx", 64); break;
            case X86_REG_RDI : return Variable("rdi", 64); break;
            case X86_REG_RSI : return Variable("rsi", 64); break;
            case X86_REG_RBP : return Variable("rbp", 64); break;
            case X86_REG_RSP : return Variable("rsp", 64); break;
        }
        throw -1;
    }
    else if (x86->operands[operand].type == X86_OP_IMM) {
        #ifdef DEBUG3
        std::cout << "get_operand X86_OP_IMM" << std::endl;
        #endif

        return Variable(x86->operands[operand].imm, x86->imm_size);
    }
}


void X86t :: ins_add ()
{
    Variable lhs = get_operand(0);
    Variable rhs = get_operand(1);
    Variable tmp = gen_tmp_var(lhs.g_bits());

    Variable OF("OF", 1);
    Variable CF("CF", 1);
    Variable ZF("ZF", 1);
    Variable SF("SF", 1);

    instructions.push_back(new InstructionAdd(tmp, lhs, rhs));

    instructions.push_back(new InstructionAssign(lhs, tmp));
}