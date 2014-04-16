#ifndef instructions_HEADER
#define instructions_HEADER

#include <list>
#include <string>

#include "instruction.h"
#include "queso.pb.h"

class Instructions {
    private :
        std::list <Instruction *> instructions;

        void delete_instructions();

    public :
        ~Instructions();
        void append (Instruction * instruction);

        Instructions & operator = (const Instructions & rhs);

        void ssa ();
        void ssa_var (std::string var_name);

        std::list <std::string> declarations ();

        std::list <Instruction *> g_instructions () { return instructions; }
        
        std::string smtlib2 ();

        std::string to_json_str ();
        bool from_json_file (std::string filename);

        std::list <Instruction *> slice_forward (Variable variable);
        std::list <Instruction *> slice_backward (Variable variable);

        bool concretize ();

        void s_copy_instructions(std::list <Instruction *> instructions);

        queso::Instructions to_queso ();
        bool from_queso_file (std::string queso_filename);
};

#endif