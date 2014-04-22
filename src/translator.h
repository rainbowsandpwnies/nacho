#ifndef translator_HEADER
#define translator_HEADER

#include <list>

#include "instruction.h"
#include "instructions.h"

class Translator {
    protected :
        Instructions instructions;

    public :
        virtual void setmem (uint8_t * mem, size_t size, uint64_t address) = 0;
        Instructions & g_instructions () { return instructions; }

        void insert_comment (std::string comment, uint64_t pc) {
        	InstructionComment * ic = new InstructionComment(comment);
        	ic->s_pc(pc);
            instructions.append(ic);
        }
};

#endif