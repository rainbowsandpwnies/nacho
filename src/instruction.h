#ifndef instruction_HEADER
#define instruction_HEADER

#include <inttypes.h>
#include <jansson.h>
#include <list>
#include <string>
#include "queso.pb.h"

#define VARIABLE_VAR   1
#define VARIABLE_CONST 2
#define VARIABLE_ARRAY 3

class Variable {
    private :
        std::string name;
        int bits;
        unsigned int addresses;
        uint64_t lval;
        int type;
        unsigned int count;

    public :
        Variable (const std::string name, int bits);
        Variable (int bits, uint64_t lval);
        Variable (const std::string name, uint64_t addresses, int bits);

        std::string  g_name () { return name; }
        int          g_bits () { return bits; }
        int          g_type () { return type; }
        unsigned int g_addresses () { return addresses; }
        unsigned int g_count () { return count; }
        uint64_t     g_lval () { return lval; }

        std::string smtlib2 ();
        std::string declare ();

        void s_count (unsigned int count);

        json_t * to_json ();
        queso::Variable to_queso ();
};


class Instruction {
    protected :
        std::string opcode;
    public :
        Instruction (std::string opcode) : opcode (opcode) {}
        virtual ~Instruction() {};
        virtual Variable * variable_written () = 0;
        virtual std::list <Variable *> variables_read () = 0;
        virtual std::list <Variable *> variables () = 0;
        virtual std::string smtlib2 () = 0 ;
        virtual json_t * to_json () = 0;
        virtual Instruction * copy () = 0;
        virtual queso::Instruction to_queso () = 0;
        std::string g_opcode () { return opcode; }
};

class InstructionComment : public Instruction {
    private :
        std::string comment;
    public :
        InstructionComment (std::string comment) : Instruction ("comment"), comment (comment) {}
        Variable * variable_written () { return NULL; }
        std::list <Variable *> variables_read () { return std::list <Variable *> (); }
        std::list <Variable *> variables () { return std::list <Variable *> (); }
        std::string smtlib2 () { return std::string("; ") + comment; }
        json_t * to_json ();
        InstructionComment * copy ();
        queso::Instruction to_queso ();

        std::string & g_comment () { return comment; }

};

class InstructionAssign : public Instruction {
    private :
        Variable dst;
        Variable src;
    public :
        InstructionAssign (const Variable & dst, const Variable & src);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionAssign * copy ();
        queso::Instruction to_queso ();

        Variable & g_dst () { return dst; }
        Variable & g_src () { return src; }
};

class InstructionStore : public Instruction {
    private :
        Variable dstmem;
        Variable srcmem;
        Variable address;
        Variable value;
        uint64_t trace_address;
        bool trace_address_set;
    public :
        InstructionStore (const Variable & mem, const Variable & address, const Variable & value);
        InstructionStore (const Variable & mem, const Variable & address, const Variable & value, uint64_t trace_address);
        InstructionStore (const Variable & dstmem, const Variable & srcmem, const Variable & address, const Variable & value);
        InstructionStore (const Variable & dstmem, const Variable & srcmem, const Variable & address, const Variable & value, uint64_t trace_address);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionStore * copy ();
        queso::Instruction to_queso ();

        void s_address (const Variable & address) { this->address = address; }

        Variable & g_srcmem () { return srcmem; }
        Variable & g_dstmem () { return dstmem; }
        Variable & g_address () { return address; }
        Variable & g_value () { return value; }
        uint64_t   g_trace_address () { return trace_address; }
        bool       g_trace_address_set () { return trace_address_set; }

        void s_trace_address (uint64_t trace_address) {
            this->trace_address = trace_address;
            trace_address_set = true;
        }
};

class InstructionLoad : public Instruction {
    private :
        Variable mem;
        Variable address;
        Variable dst;
        uint64_t trace_address;
        bool trace_address_set;
    public :
        InstructionLoad (const Variable & mem, const Variable & address, const Variable & dst);
        InstructionLoad (const Variable & mem, const Variable & address, const Variable & dst, uint64_t trace_address);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionLoad * copy ();
        queso::Instruction to_queso ();

        void s_address (const Variable & address) { this->address = address; }

        Variable & g_mem () { return mem; }
        Variable & g_address () { return address; }
        Variable & g_dst () { return dst; }
        uint64_t   g_trace_address () { return trace_address; }
        bool       g_trace_address_set () { return trace_address_set; }

        void s_trace_address (uint64_t trace_address) {
            this->trace_address = trace_address;
            trace_address_set = true;
        }
};

class InstructionIte : public Instruction {
    private :
        Variable dst;
        Variable condition;
        Variable t;
        Variable e;
    public :
        InstructionIte (const Variable & dst, const Variable & condition, const Variable & t, const Variable & e);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionIte * copy ();
        queso::Instruction to_queso ();

        Variable & g_t () { return t; }
        Variable & g_e () { return e; }
        Variable & g_dst () { return dst; }
        Variable & g_condition () { return condition; }
};

class InstructionSignExtend : public Instruction {
    private :
        Variable dst;
        Variable src;
    public :
        InstructionSignExtend (const Variable & dst, const Variable & src);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionSignExtend * copy ();
        queso::Instruction to_queso ();

        Variable & g_dst () { return dst; }
        Variable & g_src () { return src; }
};


class InstructionArithmetic : public Instruction {
    protected :
        Variable dst;
        Variable lhs;
        Variable rhs;
        std::string bvop;
        queso::Opcode quesoOpcode;
    public :
        InstructionArithmetic (const std::string & opcode, const Variable & dst, const Variable & lhs, const Variable & rhs);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionArithmetic * copy();
        queso::Instruction to_queso ();

        Variable & g_dst () { return dst; }
        Variable & g_lhs () { return lhs; }
        Variable & g_rhs () { return rhs; }
};

class InstructionAdd : public InstructionArithmetic {
    public :
        InstructionAdd (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionSub : public InstructionArithmetic {
    public :
        InstructionSub (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionMul : public InstructionArithmetic {
    public :
        InstructionMul (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionUdiv : public InstructionArithmetic {
    public :
        InstructionUdiv (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionUmod : public InstructionArithmetic {
    public :
        InstructionUmod (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionAnd : public InstructionArithmetic {
    public :
        InstructionAnd (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionOr : public InstructionArithmetic {
    public :
        InstructionOr (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionXor : public InstructionArithmetic {
    public :
        InstructionXor (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

class InstructionShr : public InstructionArithmetic {
    public :
        InstructionShr (const Variable & dst, const Variable & var, const Variable & bits);
};

class InstructionShl : public InstructionArithmetic {
    public :
        InstructionShl (const Variable & dst, const Variable & var, const Variable & bits);
};


class InstructionCmp : public Instruction {
    protected :
        Variable dst;
        Variable lhs;
        Variable rhs;
        std::string bvop;
        queso::Opcode quesoOpcode;
    public :
        InstructionCmp (const std::string & opcode, const Variable & dst, const Variable & lhs, const Variable & rhs);
        Variable * variable_written ();
        std::list <Variable *> variables_read ();
        std::list <Variable *> variables ();
        std::string smtlib2 ();
        json_t * to_json ();
        InstructionCmp * copy ();
        queso::Instruction to_queso ();

        Variable & g_dst () { return dst; }
        Variable & g_lhs () { return lhs; }
        Variable & g_rhs () { return rhs; }
};


class InstructionCmpEq : public InstructionCmp {
    public :
        InstructionCmpEq (const Variable & dst, const Variable & lhs, const Variable & rhs);
};


class InstructionCmpLtu : public InstructionCmp {
    public :
        InstructionCmpLtu (const Variable & dst, const Variable & lhs, const Variable & rhs);
};


class InstructionCmpLeu : public InstructionCmp {
    public :
        InstructionCmpLeu (const Variable & dst, const Variable & lhs, const Variable & rhs);
};


class InstructionCmpLts : public InstructionCmp {
    public :
        InstructionCmpLts (const Variable & dst, const Variable & lhs, const Variable & rhs);
};


class InstructionCmpLes : public InstructionCmp {
    public :
        InstructionCmpLes (const Variable & dst, const Variable & lhs, const Variable & rhs);
};

#endif