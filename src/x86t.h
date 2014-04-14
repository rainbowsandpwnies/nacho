#ifndef x86_translate_HEADER
#define x86_translate_HEADER


#include "instruction.h"

#include <capstone/capstone.h>
#include <inttypes.h>
#include <list>

class X86t {
    private :
        csh cshandle;
        cs_insn * insn_array;
        cs_insn * insn;
        cs_x86 * x86;
        std::list <Instruction *> instructions;

        uint16_t insn_size;
        uint32_t tmp_counter;

        void clear_instructions ();
        Variable gen_tmp_var (int bits);

        Variable get_operand (int operand);

        void ins_add ();

    public :
        X86t ();
        ~X86t ();
        std::list <Instruction *> translate (uint8_t * data, uint32_t size, uint64_t address);

        uint16_t size ();
};

#endif