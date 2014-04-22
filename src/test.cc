#include "x86t.h"
#include "instruction.h"

#include <iostream>

uint8_t bytes[] = 
{
    0x48, 0x83, 0xc3, 0x08, // add rbx, 0x8
    0x00, 0xd2, // add dl, dl
    0x48, 0x01, 0xd8, // add rax, rbx
    0x48, 0x81, 0xc4, 0x58, 0x10, 0x00, 0x00 // add rsp, 0x1058
};


int main ()
{
    X86t x86t;

    unsigned int count = 0;
    std::list <Instruction *> instructions;

    while (true) {
        instructions = x86t.translate(&(bytes[count]), sizeof(bytes) - count, count);
        if (x86t.size() == 0)
            break;
        count += x86t.size();

        std::list <Instruction *> :: iterator it;
        for (it = instructions.begin(); it != instructions.end(); it++) {
            std::cout << (*it)->smtlib2() << "\n";
        }
    }

    return 0;
}