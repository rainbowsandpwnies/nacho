#include "instruction.h"

#include <cstdio>
#include <sstream>
#include <iostream>
#include <cstring>

Variable :: Variable (const std::string name, int bits)
    : name (name), bits (bits), count (0)
{
    type = VARIABLE_VAR;
}

Variable :: Variable (int bits, uint64_t lval)
    : bits (bits), lval (lval), count (0)
{
    name = std::string("");
    type = VARIABLE_CONST;
}

Variable :: Variable (const std::string name, uint64_t addresses, int bits)
    : name (name), bits (bits), addresses (addresses), count (0)
{
    type = VARIABLE_ARRAY;
}

std::string Variable :: smtlib2 ()
{
    switch (type) {
    case VARIABLE_VAR :
    case VARIABLE_ARRAY :
        std::stringstream ss;
        ss << name << "_" << count;
        return ss.str();
    }
    char tmp[64];
    switch (bits) {
    case 1  : snprintf(tmp, 64, "#b%x", (unsigned int) lval); break;
    case 8  : snprintf(tmp, 64, "#x%02x", (unsigned int) lval); break;
    case 16 : snprintf(tmp, 64, "#x%04x", (unsigned int) lval); break;
    case 32 : snprintf(tmp, 64, "#x%08x", (unsigned int) lval); break;
    case 64 : snprintf(tmp, 64, "#x%016llx", (long long unsigned int) lval); break;
    }
    return tmp;
}

std::string Variable :: declare ()
{
    std::stringstream ss;

    switch (type) {
    case VARIABLE_VAR :
        ss << "(declare-fun " << smtlib2() << " () (_ BitVec " << bits << "))";
        return ss.str();
    case VARIABLE_ARRAY :
        ss << "(declare-fun " << smtlib2() << " () (Array (_ BitVec "
           << addresses << ") (_ BitVec " << bits << ")))";
        return ss.str();
    }

    return "";
}

void Variable :: s_count (unsigned int count)
{
    this->count = count;
}

json_t * Variable :: to_json ()
{
    json_t * var = json_object ();

    json_t * bits = json_integer(this->bits);
    json_t * count = json_integer(this->count);
    json_object_set(var, "bits", bits);
    json_object_set(var, "count", count);
    json_decref(bits);
    json_decref(count);

    switch (type) {
    case VARIABLE_VAR :
    {
        json_t * type = json_string("VAR");
        json_t * name = json_string(this->name.c_str());
        json_object_set(var, "type", type);
        json_object_set(var, "name", name);
        json_decref(type);
        json_decref(name);
        break;
    }
    case VARIABLE_ARRAY :
    {
        json_t * type = json_string("ARRAY");
        json_t * name = json_string(this->name.c_str());
        json_t * addresses = json_integer(this->addresses);
        json_object_set(var, "type", type);
        json_object_set(var, "name", name);
        json_object_set(var, "addresses", addresses);
        json_decref(type);
        json_decref(name);
        json_decref(addresses);
        break;
    }
    case VARIABLE_CONST :
    {
        json_t * type = json_string("CONST");
        json_t * lval = json_integer(this->lval);
        json_object_set(var, "type", type);
        json_object_set(var, "lval", lval);
        json_decref(type);
        json_decref(lval);
        break;
    }
    }
    return var;
}

queso::Variable Variable :: to_queso ()
{
    queso::Variable variable;
    switch (type) {
    case VARIABLE_VAR :
        variable.set_type(queso::VarType::VARIABLE);
        variable.set_name(name);
        break;
    case VARIABLE_CONST :
        variable.set_type(queso::VarType::CONSTANT);
        variable.set_lval(lval);
        break;
    case VARIABLE_ARRAY :
        variable.set_type(queso::VarType::ARRAY);
        variable.set_name(name);
        variable.set_addresses(addresses);
        break;
    }

    variable.set_bits(bits);
    variable.set_count(count);

    return variable;
}



json_t * InstructionComment :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("comment");
    json_t * comment = json_string(this->comment.c_str());

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "comment", comment);

    json_decref(opcode);
    json_decref(comment);

    return ins;
}

InstructionComment * InstructionComment :: copy ()
{
    InstructionComment * ic = new InstructionComment(comment);
    if (pc_set)
        ic->s_pc(pc);
    return ic;
}

queso::Instruction InstructionComment :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::COMMENT);
    instruction.set_comment(comment);
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}



InstructionAssign :: InstructionAssign (const Variable & dst, const Variable & src)
    : Instruction ("assign"), dst (dst), src (src)
{}

Variable * InstructionAssign :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionAssign :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&src);
    return variables;
}

std::list <Variable *> InstructionAssign :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dst);
    variables.push_back(&src);
    return variables;
}

std::string InstructionAssign :: smtlib2 ()
{
    std::stringstream ss;

    ss << "(assert (= " << dst.smtlib2() << " ";

    if (dst.g_bits() == src.g_bits())
        ss << src.smtlib2();
    else if (dst.g_bits() < src.g_bits())
        ss << "((_ extract " << dst.g_bits() - 1 << " 0) " << src.smtlib2() << ")";
    else if (dst.g_bits() > src.g_bits())
        ss << "(concat (_ bv0 " << (dst.g_bits() - src.g_bits()) << ") " << src.smtlib2() << ")";
    ss << "))";

    return ss.str();
}

json_t * InstructionAssign :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("assign");
    json_t * dst = this->dst.to_json();
    json_t * src = this->src.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "src", src);

    json_decref(opcode);
    json_decref(dst);
    json_decref(src);

    return ins;
}

InstructionAssign * InstructionAssign :: copy ()
{
    InstructionAssign * ia = new InstructionAssign(dst, src);
    if (pc_set)
        ia->s_pc(pc);
    return ia;
}

queso::Instruction InstructionAssign :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::ASSIGN);
    *(instruction.mutable_dst()) = dst.to_queso();
    *(instruction.mutable_src()) = src.to_queso();
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}



InstructionStore :: InstructionStore (const Variable & mem, const Variable & address, const Variable & value)
    : Instruction ("store"), dstmem (mem), srcmem(mem), address (address), value (value), trace_address (0), trace_address_set(false)
{}

InstructionStore :: InstructionStore (const Variable & mem, const Variable & address, const Variable & value, uint64_t trace_address)
    : Instruction ("store"), dstmem (mem), srcmem(mem), address (address), value (value), trace_address (trace_address), trace_address_set(true)
{}

InstructionStore :: InstructionStore (const Variable & dstmem, const Variable & srcmem, const Variable & address, const Variable & value)
    : Instruction ("store"), dstmem (dstmem), srcmem(srcmem), address (address), value (value), trace_address (0), trace_address_set(false)
{}

InstructionStore :: InstructionStore (const Variable & dstmem, const Variable & srcmem, const Variable & address, const Variable & value, uint64_t trace_address)
    : Instruction ("store"), dstmem (dstmem), srcmem(srcmem), address (address), value (value), trace_address (trace_address), trace_address_set(true)
{}

Variable * InstructionStore :: variable_written ()
{
    return &dstmem;
}

std::list <Variable *> InstructionStore :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&srcmem);
    variables.push_back(&address);
    variables.push_back(&value);
    return variables;
}

std::list <Variable *> InstructionStore :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dstmem);
    variables.push_back(&srcmem);
    variables.push_back(&address);
    variables.push_back(&value);
    return variables;
}

std::string InstructionStore :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dstmem.smtlib2() << " (store " << srcmem.smtlib2() << " "
       << address.smtlib2() << " " << value.smtlib2() << ")))";
    return ss.str();
}

json_t * InstructionStore :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("store");
    json_t * dstmem = this->dstmem.to_json();
    json_t * srcmem = this->srcmem.to_json();
    json_t * address = this->address.to_json();
    json_t * value = this->value.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "address", address);
    json_object_set(ins, "value", value);
    json_object_set(ins, "srcmem", srcmem);
    json_object_set(ins, "dstmem", dstmem);

    if (trace_address_set) {
        json_t * trace_address = json_integer(this->trace_address);
        json_object_set(ins, "trace_address", trace_address);
        json_decref(trace_address);
    }
    else
        std::cerr << "NO TRACE ADDRESS" << std::endl;

    json_decref(opcode);
    json_decref(address);
    json_decref(value);
    json_decref(srcmem);
    json_decref(dstmem);

    return ins;
}

InstructionStore * InstructionStore :: copy ()
{
    InstructionStore * iStore = NULL;
    if (trace_address_set)
        iStore = new InstructionStore(dstmem, srcmem, address, value, trace_address);
    else
        iStore = new InstructionStore(dstmem, srcmem, address, value);
    if (pc_set)
        iStore->s_pc(pc);
    return iStore;
}

queso::Instruction InstructionStore :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::STORE);
    *(instruction.mutable_dstmem())  = dstmem.to_queso();
    *(instruction.mutable_srcmem())  = srcmem.to_queso();
    *(instruction.mutable_address()) = address.to_queso();
    *(instruction.mutable_value())   = value.to_queso();
    if (trace_address_set)
        instruction.set_trace_address(trace_address);
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}



InstructionLoad :: InstructionLoad (const Variable & mem, const Variable & address, const Variable & dst)
    : Instruction ("load"), mem (mem), address (address), dst (dst), trace_address (0), trace_address_set (false)
{}

InstructionLoad :: InstructionLoad (const Variable & mem, const Variable & address, const Variable & dst, uint64_t trace_address)
    : Instruction ("load"), mem (mem), address (address), dst (dst), trace_address (trace_address), trace_address_set (true)
{}

Variable * InstructionLoad :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionLoad :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&mem);
    variables.push_back(&address);
    return variables;
}

std::list <Variable *> InstructionLoad :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&mem);
    variables.push_back(&address);
    variables.push_back(&dst);
    return variables;
}

std::string InstructionLoad :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dst.smtlib2() << " (select " << mem.smtlib2() << " " 
       << address.smtlib2() << ")))";
    return ss.str();
}

json_t * InstructionLoad :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("load");
    json_t * mem = this->mem.to_json();
    json_t * dst = this->dst.to_json();
    json_t * address = this->address.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "mem", mem);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "address", address);

    if (trace_address_set) {
        json_t * trace_address = json_integer(this->trace_address);
        json_object_set(ins, "trace_address", trace_address);
        json_decref(trace_address);
    }

    json_decref(mem);
    json_decref(dst);
    json_decref(address);
    return ins;
}

InstructionLoad * InstructionLoad :: copy ()
{
    InstructionLoad * il = NULL;
    if (trace_address_set)
        il = new InstructionLoad(mem, address, dst, trace_address);
    else
        il = new InstructionLoad(mem, address, dst);
    if (pc_set)
        il->s_pc(pc);
    return il;
}

queso::Instruction InstructionLoad :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::LOAD);
    *(instruction.mutable_mem())     = mem.to_queso();
    *(instruction.mutable_address()) = address.to_queso();
    *(instruction.mutable_dst())     = dst.to_queso();
    if (trace_address_set)
        instruction.set_trace_address(trace_address);
    instruction.set_pc(pc);
    return instruction;
}



InstructionIte :: InstructionIte (const Variable & dst, const Variable & condition, const Variable & t, const Variable & e)
    : Instruction ("ite"), dst (dst), condition (condition), t (t), e (e)
{}

Variable * InstructionIte :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionIte :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&condition);
    variables.push_back(&t);
    variables.push_back(&e);
    return variables;
}

std::list <Variable *> InstructionIte :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dst);
    variables.push_back(&condition);
    variables.push_back(&t);
    variables.push_back(&e);
    return variables;
}

std::string InstructionIte :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dst.smtlib2() << " (ite (= " << condition.smtlib2() << " #b1) "
       << t.smtlib2() << " " << e.smtlib2() << ")))";
    return ss.str();
}

json_t * InstructionIte :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("ite");
    json_t * dst = this->dst.to_json();
    json_t * condition = this->condition.to_json();
    json_t * t = this->t.to_json();
    json_t * e = this->e.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "condition", condition);
    json_object_set(ins, "t", t);
    json_object_set(ins, "e", e);

    json_decref(opcode);
    json_decref(dst);
    json_decref(condition);
    json_decref(t);
    json_decref(e);

    return ins;
}

InstructionIte * InstructionIte :: copy ()
{
    InstructionIte * ii = new InstructionIte(dst, condition, t, e);
    if (pc_set)
        ii->s_pc(pc);
    return ii;
}

queso::Instruction InstructionIte :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::ITE);
    *(instruction.mutable_dst())       = dst.to_queso();
    *(instruction.mutable_condition()) = condition.to_queso();
    *(instruction.mutable_t())         = t.to_queso();
    *(instruction.mutable_e())         = e.to_queso();
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}



InstructionSignExtend :: InstructionSignExtend (const Variable & dst, const Variable & src)
    : Instruction ("signextend"), dst (dst), src (src)
{}

Variable * InstructionSignExtend :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionSignExtend :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&src);
    return variables;
}

std::list <Variable *> InstructionSignExtend :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dst);
    variables.push_back(&src);
    return variables;
}

std::string InstructionSignExtend :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dst.smtlib2() << " ((_ sign_extend ";
    ss << dst.g_bits() << ") " << src.smtlib2() << ")))";
    return ss.str();
}

json_t * InstructionSignExtend :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string("signextend");
    json_t * dst = this->dst.to_json();
    json_t * src = this->src.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "src", src);

    json_decref(opcode);
    json_decref(dst);
    json_decref(src);

    return ins;
}

InstructionSignExtend * InstructionSignExtend :: copy ()
{
    InstructionSignExtend * is = new InstructionSignExtend(dst, src);
    if (pc_set)
        is->s_pc(pc);
    return is;
}

queso::Instruction InstructionSignExtend :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(queso::Opcode::SIGNEXTEND);
    *(instruction.mutable_dst()) = dst.to_queso();
    *(instruction.mutable_src()) = src.to_queso();
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}



InstructionArithmetic :: InstructionArithmetic (const std::string & opcode, const Variable & dst, const Variable & lhs, const Variable & rhs)
    : Instruction (opcode), dst (dst), lhs (lhs), rhs (rhs)
{}

Variable * InstructionArithmetic :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionArithmetic :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&lhs);
    variables.push_back(&rhs);
    return variables;
}

std::list <Variable *> InstructionArithmetic :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dst);
    variables.push_back(&lhs);
    variables.push_back(&rhs);
    return variables;
}

std::string InstructionArithmetic :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dst.smtlib2() << " (" << bvop << " " << lhs.smtlib2() << " " << rhs.smtlib2() << ")))";
    return ss.str();
}

json_t * InstructionArithmetic :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string(this->opcode.c_str());
    json_t * dst = this->dst.to_json();
    json_t * lhs = this->lhs.to_json();
    json_t * rhs = this->rhs.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "lhs", lhs);
    json_object_set(ins, "rhs", rhs);

    json_decref(opcode);
    json_decref(dst);
    json_decref(lhs);
    json_decref(rhs);

    return ins;
}

InstructionArithmetic * InstructionArithmetic :: copy ()
{
    InstructionArithmetic * ia = new InstructionArithmetic(opcode, dst, lhs, rhs);
    ia->bvop = this->bvop;
    ia->quesoOpcode = this->quesoOpcode;
    if (pc_set)
        ia->s_pc(pc);
    return ia;
}

queso::Instruction InstructionArithmetic :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(quesoOpcode);
    *(instruction.mutable_dst()) = dst.to_queso();
    *(instruction.mutable_lhs()) = lhs.to_queso();
    *(instruction.mutable_rhs()) = rhs.to_queso();
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}




InstructionAdd :: InstructionAdd (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("add", dst, a, b)
{
    bvop = "bvadd";
    quesoOpcode = queso::Opcode::ADD;
}



InstructionSub :: InstructionSub (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("sub", dst, a, b)
{
    bvop = "bvsub";
    quesoOpcode = queso::Opcode::SUB;
}



InstructionMul :: InstructionMul (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("mul", dst, a, b)
{
    bvop = "bvmul";
    quesoOpcode = queso::Opcode::MUL;
}



InstructionUdiv :: InstructionUdiv (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("udiv", dst, a, b)
{
    bvop = "bvudiv";
    quesoOpcode = queso::Opcode::UDIV;
}



InstructionUmod :: InstructionUmod (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("umod", dst, a, b)
{
    bvop = "bvumod";
    quesoOpcode = queso::Opcode::UMOD;
}



InstructionAnd :: InstructionAnd (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("and", dst, a, b)
{
    bvop = "bvand";
    quesoOpcode = queso::Opcode::AND;
}



InstructionOr :: InstructionOr (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("or", dst, a, b)
{
    bvop = "bvor";
    quesoOpcode = queso::Opcode::OR;
}



InstructionXor :: InstructionXor (const Variable & dst, const Variable & a, const Variable & b)
    : InstructionArithmetic("xor", dst, a, b)
{
    bvop = "bvxor";
    quesoOpcode = queso::Opcode::XOR;
}


InstructionShr :: InstructionShr (const Variable & dst, const Variable & var, const Variable & bits)
    : InstructionArithmetic("shr", dst, var, bits)
{
    bvop = "bvlshr";
    quesoOpcode = queso::Opcode::SHR;
}


InstructionShl :: InstructionShl (const Variable & dst, const Variable & var, const Variable & bits)
    : InstructionArithmetic("shl", dst, var, bits)
{
    bvop = "bvshl";
    quesoOpcode = queso::Opcode::SHL;
}



InstructionCmp :: InstructionCmp (const std::string & opcode, const Variable & dst, const Variable & lhs, const Variable & rhs)
    : Instruction (opcode), dst (dst), lhs (lhs), rhs (rhs)
{}

Variable * InstructionCmp :: variable_written ()
{
    return &dst;
}

std::list <Variable *> InstructionCmp :: variables_read ()
{
    std::list <Variable *> variables;
    variables.push_back(&lhs);
    variables.push_back(&rhs);
    return variables;
}

std::list <Variable *> InstructionCmp :: variables ()
{
    std::list <Variable *> variables;
    variables.push_back(&dst);
    variables.push_back(&lhs);
    variables.push_back(&rhs);
    return variables;
}

std::string InstructionCmp :: smtlib2 ()
{
    std::stringstream ss;
    ss << "(assert (= " << dst.smtlib2() << " (ite ("
       << bvop << " " << lhs.smtlib2() << " " << rhs.smtlib2() << ") #b1 #b0)))";
    return ss.str();
}

json_t * InstructionCmp :: to_json ()
{
    json_t * ins = json_object();
    json_t * opcode = json_string(this->opcode.c_str());
    json_t * dst = this->dst.to_json();
    json_t * lhs = this->lhs.to_json();
    json_t * rhs = this->rhs.to_json();

    json_object_set(ins, "opcode", opcode);
    json_object_set(ins, "dst", dst);
    json_object_set(ins, "lhs", lhs);
    json_object_set(ins, "rhs", rhs);

    json_decref(opcode);
    json_decref(dst);
    json_decref(lhs);
    json_decref(rhs);

    return ins;
}

InstructionCmp * InstructionCmp :: copy ()
{
    InstructionCmp * ic = new InstructionCmp(opcode, dst, lhs, rhs);
    ic->bvop = this->bvop;
    ic->quesoOpcode = this->quesoOpcode;
    if (pc_set)
        ic->s_pc(pc);
    return ic;
}

queso::Instruction InstructionCmp :: to_queso ()
{
    queso::Instruction instruction;
    instruction.set_opcode(quesoOpcode);
    *(instruction.mutable_dst()) = dst.to_queso();
    *(instruction.mutable_lhs()) = lhs.to_queso();
    *(instruction.mutable_rhs()) = rhs.to_queso();
    if (pc_set)
        instruction.set_pc(pc);
    return instruction;
}


InstructionCmpEq :: InstructionCmpEq (const Variable & dst, const Variable & lhs, const Variable & rhs)
    : InstructionCmp("cmpeq", dst, lhs, rhs)
{
    bvop = "=";
    quesoOpcode = queso::Opcode::CMPEQ;
}


InstructionCmpLtu :: InstructionCmpLtu (const Variable & dst, const Variable & lhs, const Variable & rhs)
    : InstructionCmp("cmpltu", dst, lhs, rhs)
{
    bvop = "bvlt";
    quesoOpcode = queso::Opcode::CMPLTU;
}


InstructionCmpLeu :: InstructionCmpLeu (const Variable & dst, const Variable & lhs, const Variable & rhs)
    : InstructionCmp("cmpleu", dst, lhs, rhs)
{
    bvop = "bvle";
    quesoOpcode = queso::Opcode::CMPLEU;
}


InstructionCmpLts :: InstructionCmpLts (const Variable & dst, const Variable & lhs, const Variable & rhs)
    : InstructionCmp("cmplts", dst, lhs, rhs)
{
    bvop = "sbvlt";
    quesoOpcode = queso::Opcode::CMPLTS;
}


InstructionCmpLes :: InstructionCmpLes (const Variable & dst, const Variable & lhs, const Variable & rhs)
    : InstructionCmp("cmples", dst, lhs, rhs)
{
    bvop = "sbvle";
    quesoOpcode = queso::Opcode::CMPLES;
}