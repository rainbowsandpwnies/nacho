#include "hsvmt.h"

#include "translator.h"
#include "queso.pb.h"

#include <jansson.h>
#include <iostream>

int main (int argc, char * argv[])
{
    Hsvmt hsvmt;
    
    json_t * root = json_load_file(argv[1], 0, NULL);

    for (unsigned int step_i = 0; step_i < json_array_size(root); step_i++) {
        json_t * step = json_array_get(root, step_i);

        json_t * memory = json_object_get(step, "memory");
        if (memory != NULL) {
            size_t size = json_array_size(memory);
            uint8_t * membuf = (uint8_t *) malloc(size);
            uint64_t address = json_integer_value(json_object_get(step, "address"));

            for (size_t i = 0; i < size; i++) {
                membuf[i] = (uint8_t) json_integer_value(json_array_get(memory, i));
            }
            hsvmt.setmem(membuf, size, address);
            free(membuf);
            continue;
        }

        uint8_t bytes[4];
        bytes[0] = json_integer_value(json_array_get(json_object_get(step, "bytes"), 0));
        bytes[1] = json_integer_value(json_array_get(json_object_get(step, "bytes"), 1));
        bytes[2] = json_integer_value(json_array_get(json_object_get(step, "bytes"), 2));
        bytes[3] = json_integer_value(json_array_get(json_object_get(step, "bytes"), 3));

        std::string ins_text = json_string_value(json_object_get(json_array_get(root, step_i), "text"));
        
        //std::cout << ins_text << std::endl;

        json_t * mem_address_ = json_object_get(step, "mem_address");
        uint64_t mem_address = 0;
        if (mem_address_ != NULL)
            mem_address = json_integer_value(mem_address_);

        uint16_t rip = (uint16_t) json_integer_value(json_object_get(step, "rip"));
        char tmp[128];
        snprintf(tmp, 128, "%04x %s", rip, ins_text.c_str());
        hsvmt.insert_comment(tmp, rip);
        hsvmt.translate(bytes, 4, rip, mem_address);
    }

    json_decref(root);

    //ssa(instructions);

    Instructions instructions;
    instructions.s_copy_instructions(hsvmt.g_instructions().g_instructions());
    instructions.ssa();
    queso::Instructions qInstructions = instructions.to_queso();
    qInstructions.SerializeToOstream(&(std::cout));

    /*

    std::cout << "(set-option :produce-models true)" << std::endl;
    std::cout << "(set-logic QF_AUFBV)" << std::endl;
    std::cout << "(set-info :smt-lib-version 2.0)" << std::endl;

    Instructions instructions = hsvmt.g_instructions();
    instructions.ssa();

    std::list <std::string> declarations = instructions.declarations();
    std::list <std::string> :: iterator sit;
    for (sit = declarations.begin(); sit != declarations.end(); sit++) {
        std::cout << *sit << std::endl;
    }


    std::list <Instruction *> ins = instructions.g_instructions();
    std::list <Instruction *> :: iterator it;
    for (it = ins.begin(); it != ins.end(); it++) {
        std::cout << (*it)->smtlib2() << std::endl;
    }

    std::cout << "(check-sat)" << std::endl;
    std::cout << "(get-value (r1_0 r1_1 r1_2 r1_3 r1_4 r1_5 r1_6 r1_7 r1_8 r1_9 r1_10))" << std::endl;

    */

    return 0;
}