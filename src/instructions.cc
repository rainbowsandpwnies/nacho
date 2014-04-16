#include "instructions.h"

#include <fstream>
#include <map>
#include <unordered_set>
#include <jansson.h>
#include <iostream>
#include <sstream>


void Instructions :: delete_instructions ()
{
    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        delete instruction;
    }
    instructions.clear();
}

Instructions :: ~Instructions ()
{

    delete_instructions();
}

void Instructions :: s_copy_instructions (std::list <Instruction *> instructions) {
    delete_instructions();

    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++) {
        append((*it)->copy());
    }
}

void Instructions :: append (Instruction * instruction)
{
    instructions.push_back(instruction);
}


Instructions & Instructions :: operator = (const Instructions & rhs)
{
    if (this == &rhs)
        return *this;

    std::list <Instruction *> :: const_iterator it;
    for (it = rhs.instructions.begin(); it != rhs.instructions.end(); it++) {
        append((*it)->copy());
    }

    return *this;
}


void Instructions :: ssa ()
{

    std::map <std::string, unsigned int> counts;

    std::list <Instruction *> :: iterator it;

    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        
        // set read vars
        std::list <Variable *> read_vars = instruction->variables_read();
        std::list <Variable *> :: iterator vit;
        for (vit = read_vars.begin(); vit != read_vars.end(); vit++) {
            Variable * variable = *vit;
            if (variable->g_type() == VARIABLE_CONST)
                continue;
            if (counts.count(variable->g_name()) == 0)
                counts[variable->g_name()] = 0;
            else
                variable->s_count(counts[variable->g_name()]);
        }

        // set write var
        Variable * variable = instruction->variable_written();
        if (variable == NULL)
            continue;
        if (counts.count(variable->g_name()) == 0)
            counts[variable->g_name()] = 0;
        else {
            counts[variable->g_name()] += 1;
            variable->s_count(counts[variable->g_name()]);
        }
    }

}


std::string Instructions :: smtlib2 ()
{
    std::stringstream smtlib2;

    smtlib2 << "(set-option :produce-models true)" << std::endl;
    smtlib2 << "(set-logic QF_AUFBV)" << std::endl;
    smtlib2 << "(set-info :smt-lib-version 2.0)" << std::endl;

    std::list <std::string> declarations = this->declarations();
    std::list <std::string> :: iterator dit;
    for (dit = declarations.begin(); dit != declarations.end(); dit++) {
        smtlib2 << (*dit) << std::endl;
    }

    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        smtlib2 << instruction->smtlib2() << std::endl;
    }

    return smtlib2.str();
}


void Instructions :: ssa_var (std::string var_name)
{

    unsigned int count = 0;

    std::list <Instruction *> :: iterator it;

    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        
        // set read vars
        std::list <Variable *> read_vars = instruction->variables_read();
        std::list <Variable *> :: iterator vit;
        for (vit = read_vars.begin(); vit != read_vars.end(); vit++) {
            Variable * variable = *vit;
            if (variable->g_type() == VARIABLE_CONST)
                continue;
            if (variable->g_name() == var_name)
                variable->s_count(count);
        }

        // set write var
        Variable * variable = instruction->variable_written();
        if (variable == NULL)
            continue;
        if (variable->g_name() == var_name)
            variable->s_count(++count);
    }

}


std::list <std::string> Instructions :: declarations ()
{
    std::map <std::string, std::string> decs;

    std::list <Instruction *> :: iterator it;

    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        std::list <Variable *> variables = instruction->variables();
        std::list <Variable *> :: iterator vit;
        for (vit = variables.begin(); vit != variables.end(); vit++) {
            Variable * variable = *vit;
            if (variable->g_type() == VARIABLE_CONST)
                continue;
            if (decs.count(variable->smtlib2()) == 0)
                decs[variable->smtlib2()] = variable->declare();
        }
    }

    std::list <std::string> result;
    std::map <std::string, std::string> :: iterator mit;
    for (mit = decs.begin(); mit != decs.end(); mit++) {
        result.push_back(mit->second);
    }

    return result;
}


std::string Instructions :: to_json_str ()
{
    json_t * root = json_array();

    std::list <Instruction *> :: iterator it;
    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;
        json_t * json_ins = instruction->to_json();
        json_array_append(root, json_ins);
        json_decref(json_ins);
    }

    char * tmp = json_dumps(root, JSON_INDENT(2));
    std::string json_str = tmp;
    free(tmp);
    json_decref(root);

    return json_str;
}


Variable variable_from_json (json_t * json_var)
{
    Variable variable = Variable(1, 2);

    json_t * type = json_object_get(json_var, "type");
    json_t * bits = json_object_get(json_var, "bits");
    json_t * count = json_object_get(json_var, "count");

    std::string type_str = json_string_value(type);
    if (type_str == "VAR") {
        json_t * name = json_object_get(json_var, "name");
        variable = Variable(json_string_value(name), json_integer_value(bits));
    }
    else if (type_str == "ARRAY") {
        json_t * name = json_object_get(json_var, "name");
        json_t * addresses = json_object_get(json_var, "addresses");
        variable = Variable(json_string_value(name), json_integer_value(addresses), json_integer_value(bits));
    }
    else if (type_str == "CONST") {
        json_t * lval = json_object_get(json_var, "lval");
        variable = Variable((int) json_integer_value(bits), (uint64_t) json_integer_value(lval));
        if (variable.g_type() != VARIABLE_CONST) {
            std::cerr << "const variable is of type " << variable.g_type() << std::endl;
            throw -1;
        }

    }

    variable.s_count(json_integer_value(count));

    return variable;
}


bool Instructions :: from_json_file (std::string filename)
{
    instructions.clear();

    json_error_t json_error;
    json_t * root = json_load_file(filename.c_str(), 0, &json_error);
    if (root == NULL) {
        std::cerr << json_error.text << std::endl;
        return false;
    }

    for (unsigned int i = 0; i < json_array_size(root); i++) {
        json_t * step = json_array_get(root, i);
        json_t * opcode = json_object_get(step, "opcode");
        std::string opcode_str = json_string_value(opcode);

        if (opcode_str == "comment") {
            json_t * comment = json_object_get(step, "comment");
            append(new InstructionComment(json_string_value(comment)));
        }
        else if (opcode_str == "store") {
            Variable address = variable_from_json(json_object_get(step, "address"));
            Variable value = variable_from_json(json_object_get(step, "value"));
            Variable srcmem = variable_from_json(json_object_get(step, "srcmem"));
            Variable dstmem = variable_from_json(json_object_get(step, "dstmem"));
            json_t * trace_address = json_object_get(step, "trace_address");
            if (trace_address != NULL) {
                append(new InstructionStore(dstmem, srcmem, address, value, json_integer_value(trace_address)));
            }
            else
                append(new InstructionStore(dstmem, srcmem, address, value));
        }
        else if (    (opcode_str == "add") || (opcode_str == "sub")
                  || (opcode_str == "xor") || (opcode_str == "and")
                  || (opcode_str == "shr") || (opcode_str == "shl")
                  || (opcode_str == "or")) {
            Variable dst = variable_from_json(json_object_get(step, "dst"));
            Variable lhs = variable_from_json(json_object_get(step, "lhs"));
            Variable rhs = variable_from_json(json_object_get(step, "rhs"));
            if (opcode_str == "add")
                append(new InstructionAdd(dst, lhs, rhs));
            else if (opcode_str == "sub")
                append(new InstructionSub(dst, lhs, rhs));
            else if (opcode_str == "xor")
                append(new InstructionXor(dst, lhs, rhs));
            else if (opcode_str == "and")
                append(new InstructionAnd(dst, lhs, rhs));
            else if (opcode_str == "shr")
                append(new InstructionShr(dst, lhs, rhs));
            else if (opcode_str == "shl")
                append(new InstructionShl(dst, lhs, rhs));
            else if (opcode_str == "or")
                append(new InstructionOr(dst, lhs, rhs));
        }
        else if (opcode_str == "load") {
            Variable mem = variable_from_json(json_object_get(step, "mem"));
            Variable dst = variable_from_json(json_object_get(step, "dst"));
            Variable address = variable_from_json(json_object_get(step, "address"));
            json_t * trace_address = json_object_get(step, "trace_address");
            if (trace_address != NULL) {
                append(new InstructionLoad(mem, address, dst, json_integer_value(trace_address)));
            }
            else
                append(new InstructionLoad(mem, address, dst));
        }
        else if (opcode_str == "assign") {
            Variable dst = variable_from_json(json_object_get(step, "dst"));
            Variable src = variable_from_json(json_object_get(step, "src"));
            append(new InstructionAssign(dst, src));
        }
        else if (opcode_str == "cmpeq") {
            Variable dst = variable_from_json(json_object_get(step, "dst"));
            Variable lhs = variable_from_json(json_object_get(step, "lhs"));
            Variable rhs = variable_from_json(json_object_get(step, "rhs"));
            append(new InstructionCmpEq(dst, lhs, rhs));
        }
        else if (opcode_str == "ite") {
            Variable dst = variable_from_json(json_object_get(step, "dst"));
            Variable condition = variable_from_json(json_object_get(step, "condition"));
            Variable t = variable_from_json(json_object_get(step, "t"));
            Variable e = variable_from_json(json_object_get(step, "e"));
            append(new InstructionIte(dst, condition, t, e));
        }
        else {
            std::cout << "unhandled instruction " << opcode_str << std::endl;
            throw -1;
        }
    }
    json_decref(root);
    return true;
}


std::list <Instruction *> Instructions :: slice_forward (Variable variable) {
    std::unordered_set <std::string> trace_vars;
    trace_vars.insert(variable.smtlib2());

    std::list <Instruction *> slice_instructions;

    std::list <Instruction *> :: iterator it;
    // for every instruction in this trace
    for (it = instructions.begin(); it != instructions.end(); it++) {
        Instruction * instruction = *it;

        std::list <std::string> variable_strings;

        std::string dstvar;

        // we treat load/store special case
        InstructionStore * iStore = dynamic_cast<InstructionStore *> (instruction);
        InstructionLoad  * iLoad  = dynamic_cast<InstructionLoad *>  (instruction);
        InstructionIte   * iIte   = dynamic_cast<InstructionIte *>   (instruction);
        if (iStore != NULL) {
            variable_strings.push_back(iStore->g_address().smtlib2());
            variable_strings.push_back(iStore->g_value().smtlib2());
            std::stringstream dstvarss;
            dstvarss << iStore->g_dstmem().g_name() << "=>" << iStore->g_trace_address();
            dstvar = dstvarss.str();
        }
        else if (iLoad != NULL) {
            std::stringstream srcvarss;
            srcvarss << iLoad->g_mem().g_name() << "=>" << iLoad->g_trace_address();
            variable_strings.push_back(srcvarss.str());
            variable_strings.push_back(iLoad->g_address().smtlib2());
            dstvar = iLoad->g_dst().smtlib2();
        }
        else if (iIte != NULL) {
            variable_strings.push_back(iIte->g_t().smtlib2());
            variable_strings.push_back(iIte->g_e().smtlib2());
            dstvar = iIte->g_dst().smtlib2();
        }
        else {
            std::list <Variable *> variables = instruction->variables_read();
            std::list <Variable *> :: iterator vit;
            for (vit = variables.begin(); vit != variables.end(); vit++) {
                variable_strings.push_back((*vit)->smtlib2());
            }
            if (instruction->variable_written() != NULL)
                dstvar = instruction->variable_written()->smtlib2();
        }

        std::list <std::string> :: iterator vsit;
        bool tainted = false;
        // check every read variable
        for (vsit = variable_strings.begin(); vsit != variable_strings.end(); vsit++) {

            if (trace_vars.count((*vsit)) > 0) {
                // add written variable to trace_vars
                if (trace_vars.count(dstvar) == 0)
                    trace_vars.insert(dstvar);
                tainted = true;
                // and log this instruction
                slice_instructions.push_back(instruction);
                break;
            }
        }

        if (tainted == false)
            trace_vars.erase(dstvar);
    }

    return slice_instructions;
}


std::list <Instruction *> Instructions :: slice_backward (Variable variable) {
    std::unordered_set <std::string> trace_vars;
    trace_vars.insert(variable.smtlib2());

    std::list <Instruction *> slice_instructions;

    std::list <Instruction *> :: reverse_iterator it;
    // for every instruction in this trace
    for (it = instructions.rbegin(); it != instructions.rend(); it++) {
        Instruction * instruction = *it;

        std::list <std::string> variable_strings;

        std::string dstvar;

        // we treat load/store special case
        InstructionStore * iStore = dynamic_cast<InstructionStore *> (instruction);
        InstructionLoad  * iLoad  = dynamic_cast<InstructionLoad *>  (instruction);
        if (iStore != NULL) {
            variable_strings.push_back(iStore->g_address().smtlib2());
            variable_strings.push_back(iStore->g_value().smtlib2());
            std::stringstream dstvarss;
            //if (iStore->g_trace_address_set() == false)
            //    std::cerr << "trace address not set: " << iStore->smtlib2() << std::endl;
            dstvarss << iStore->g_dstmem().g_name() << "=>" << iStore->g_trace_address();
            dstvar = dstvarss.str();
        }
        else if (iLoad != NULL) {
            std::stringstream srcvarss;
            srcvarss << iLoad->g_mem().g_name() << "=>" << iLoad->g_trace_address();
            variable_strings.push_back(srcvarss.str());
            variable_strings.push_back(iLoad->g_address().smtlib2());
            dstvar = iLoad->g_dst().smtlib2();
        }
        else {
            std::list <Variable *> variables = instruction->variables_read();
            std::list <Variable *> :: iterator vit;
            for (vit = variables.begin(); vit != variables.end(); vit++) {
                variable_strings.push_back((*vit)->smtlib2());
            }
            if (instruction->variable_written() != NULL)
                dstvar = instruction->variable_written()->smtlib2();
        }

        std::list <std::string> :: iterator vsit;
        // check if the dst var is in our tainted set
        if (trace_vars.count(dstvar) > 0) {
            // remove dstvar from tainted set
            trace_vars.erase(dstvar);
            // add all source vars to our tainted set
            for (vsit = variable_strings.begin(); vsit != variable_strings.end(); vsit++) {
                trace_vars.insert(*vsit);
            }
            slice_instructions.push_back(instruction);
        }
    }

    slice_instructions.reverse();

    return slice_instructions;
}


bool Instructions :: concretize ()
{
    std::list <Instruction *> :: iterator it;

    for (it = instructions.begin(); it != instructions.end(); it++) {
        InstructionStore * iStore = dynamic_cast <InstructionStore *>(*it);
        if (iStore != NULL) {
            if (iStore->g_trace_address_set() == false)
                return false;
            iStore->s_address(Variable(iStore->g_dstmem().g_bits(), iStore->g_trace_address()));
            continue;
        }
        InstructionLoad * iLoad = dynamic_cast <InstructionLoad *>(*it);
        if (iLoad != NULL) {
            if (iLoad->g_trace_address_set() == false)
                return false;
            iLoad->s_address(Variable(iLoad->g_mem().g_bits(), iLoad->g_trace_address()));
            continue;
        }
    }
    return true;
}


queso::Instructions Instructions :: to_queso ()
{
    queso::Instructions instructions;

    std::list <Instruction *> :: iterator it;
    for (it = this->instructions.begin(); it != this->instructions.end(); it++) {
        *(instructions.add_instruction()) = (*it)->to_queso();
    }

    return instructions;
}


Variable variable_from_queso (queso::Variable qVariable)
{
    Variable variable = Variable((int) 0, (uint64_t) 0);
    switch (qVariable.type()) {
    case queso::VarType::VARIABLE :
        variable = Variable(qVariable.name(), qVariable.bits());
        variable.s_count(qVariable.count());
        break;
    case queso::VarType::CONSTANT :
        variable = Variable(qVariable.bits(), qVariable.lval());
        variable.s_count(qVariable.count());
        break;
    case queso::VarType::ARRAY :
        variable = Variable(qVariable.name(), qVariable.addresses(), qVariable.bits());
        variable.s_count(qVariable.count());
        break;
    default :
        throw -9;
    }
    return variable;
}


bool Instructions :: from_queso_file (std::string queso_filename)
{
    delete_instructions();

    std::ifstream quesoFile;
    quesoFile.open(queso_filename);

    queso::Instructions instructions;
    instructions.ParseFromIstream(&quesoFile);
    quesoFile.close();

    for (int i = 0; i < instructions.instruction_size(); i++) {
        queso::Instruction instruction = instructions.instruction(i);

        switch (instruction.opcode()) {
        case queso::Opcode::COMMENT :
            append(new InstructionComment(instruction.comment()));
            break;
        case queso::Opcode::ASSIGN :
        {
            Variable dst = variable_from_queso(instruction.dst());
            Variable src = variable_from_queso(instruction.src());
            append(new InstructionAssign(dst, src));
            break;
        }
        case queso::Opcode::STORE :
        {
            Variable dstmem = variable_from_queso(instruction.dstmem());
            Variable srcmem = variable_from_queso(instruction.srcmem());
            Variable address = variable_from_queso(instruction.address());
            Variable value = variable_from_queso(instruction.value());
            InstructionStore * is = new InstructionStore(dstmem, srcmem, address, value);
            if (instruction.has_trace_address())
                is->s_trace_address(instruction.trace_address());
            append(is);
            break;
        }
        case queso::Opcode::LOAD :
        {
            Variable mem = variable_from_queso(instruction.mem());
            Variable address = variable_from_queso(instruction.address());
            Variable dst = variable_from_queso(instruction.dst());
            InstructionLoad * il = new InstructionLoad(mem, address, dst);
            if (instruction.has_trace_address())
                il->s_trace_address(instruction.trace_address());
            append(il);
            break;
        }
        case queso::Opcode::ITE :
        {
            Variable dst = variable_from_queso(instruction.dst());
            Variable condition = variable_from_queso(instruction.condition());
            Variable t = variable_from_queso(instruction.t());
            Variable e = variable_from_queso(instruction.e());
            append(new InstructionIte(dst, condition, t, e));
            break;
        }
        case queso::Opcode::SIGNEXTEND :
        {
            Variable dst = variable_from_queso(instruction.dst());
            Variable src = variable_from_queso(instruction.src());
            append(new InstructionSignExtend(dst, src));
            break;
        }
        case queso::Opcode::ADD  :
        case queso::Opcode::SUB  :
        case queso::Opcode::MUL  :
        case queso::Opcode::UDIV :
        case queso::Opcode::UMOD :
        case queso::Opcode::AND  :
        case queso::Opcode::OR   :
        case queso::Opcode::XOR  :
        case queso::Opcode::SHR  :
        case queso::Opcode::SHL  :
        {
            Variable dst = variable_from_queso(instruction.dst());
            Variable lhs = variable_from_queso(instruction.lhs());
            Variable rhs = variable_from_queso(instruction.rhs());

            if (instruction.opcode() == queso::Opcode::ADD)
                append(new InstructionAdd(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::SUB)
                append(new InstructionSub(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::MUL)
                append(new InstructionMul(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::UDIV)
                append(new InstructionUdiv(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::UMOD)
                append(new InstructionUmod(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::AND)
                append(new InstructionAnd(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::OR)
                append(new InstructionOr(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::XOR)
                append(new InstructionXor(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::SHR)
                append(new InstructionShr(dst, lhs, rhs));

            else if (instruction.opcode() == queso::Opcode::SHL)
                append(new InstructionShl(dst, lhs, rhs));

            break;
        }
        case queso::Opcode::CMPEQ :
        case queso::Opcode::CMPLTU :
        case queso::Opcode::CMPLEU :
        case queso::Opcode::CMPLTS :
        case queso::Opcode::CMPLES :
        {
            Variable dst = variable_from_queso(instruction.dst());
            Variable lhs = variable_from_queso(instruction.lhs());
            Variable rhs = variable_from_queso(instruction.rhs());
            if (instruction.opcode() == queso::Opcode::CMPEQ)
                append(new InstructionCmpEq(dst, lhs, rhs));
            else if (instruction.opcode() == queso::Opcode::CMPLTU)
                append(new InstructionCmpLtu(dst, lhs, rhs));
            else if (instruction.opcode() == queso::Opcode::CMPLEU)
                append(new InstructionCmpLeu(dst, lhs, rhs));
            else if (instruction.opcode() == queso::Opcode::CMPLTS)
                append(new InstructionCmpLts(dst, lhs, rhs));
            else if (instruction.opcode() == queso::Opcode::CMPLES)
                append(new InstructionCmpLes(dst, lhs, rhs));
            break;
        }
        default :
            throw -8;
        }
    }

    return true;
}