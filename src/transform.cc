#include "translator.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <unistd.h>
#include <getopt.h>

static struct option long_options [] = {
    {"ssa", no_argument, 0, 'a'},
    {"backwardslice", required_argument, 0, 'b'},
    {"concretize", no_argument, 0, 'c'},
    {"help", no_argument, 0, 'h'},
    {"ilfile", required_argument, 0, 'i'},
    {"forwardslice", required_argument, 0, 'l'},
    {"iqueso", required_argument, 0, 'n'},
    {"output", required_argument, 0, 'o'},
    {"queso", required_argument, 0, 'q'},
    {"smtlib2", required_argument, 0, 's'},
    {0, 0, 0, 0}
};

Variable parseVarString (const char * varstring) {
    char * tmp = (char *) malloc(strlen(varstring) + 1);
    strcpy(tmp, varstring);

    // can we split count from varname?
    unsigned int underscore_location;
    for (underscore_location = strlen(tmp); underscore_location > 0; underscore_location--) {
        if (tmp[underscore_location] == '_')
            break;
    }

    unsigned int varcount = 0;
    
    if (underscore_location != '\0') {
        tmp[underscore_location] = '\0';
        varcount = strtoul(&(tmp[underscore_location+1]), NULL, 10);
    }
    std::string varname = tmp;

    Variable variable = Variable(tmp, 0);
    variable.s_count(varcount);

    free(tmp);

    return variable;
}

int main (int argc, char * argv [])
{
    char * ilfilename = NULL;
    char * smtlib2filename = NULL;
    char * outputfilename = NULL;
    char * quesofilename = NULL;
    char * forwardslicevarname = NULL;
    char * backwardslicevarname = NULL;
    char * iquesofilename = NULL;
    bool dossa = false;
    bool concretize = false;
    int option_index = 0;

    GOOGLE_PROTOBUF_VERIFY_VERSION;

    bool parseloop = true;
    while (parseloop) {
        int c = getopt_long (argc, argv, "ab:chi:l:n:o:q:s:", long_options, &option_index);
        switch (c) {
            case 'a' :
                dossa = true;
                break;
            case 'b' :
                backwardslicevarname = optarg;
                break;
            case 'c' :
                concretize = true;
                break;
            case 'h' :
                std::cout << "il translator" << std::endl;
                std::cout << "-a --ssa                      static single assigment" << std::endl;
                std::cout << "-b --backwardslice var_name   backward slice var trace" << std::endl;
                std::cout << "-c --concretize               concretize values" << std::endl;
                std::cout << "-h --help                     this help message" << std::endl;
                std::cout << "-i --ifile FILE               input il json file" << std::endl;
                std::cout << "-l --forwardslice var_name    forward slice var trace" << std::endl;
                std::cout << "-n --iqueso FILE              input queso file" << std::endl;
                std::cout << "-o --output FILE              output il json file" << std::endl;
                std::cout << "-q --queso FILE               output queso file" << std::endl;
                std::cout << "-s --smtlib2 FILE             output smtlib2 file" << std::endl;
                return 0;
            case 'i' :
                ilfilename = optarg;
                break;
            case 'l' :
                forwardslicevarname = optarg;
                break;
            case 'n' :
                iquesofilename = optarg;
                break;
            case 'o' :
                outputfilename = optarg;
                break;
            case 'q' :
                quesofilename = optarg;
                break;
            case 's' :
                smtlib2filename = optarg;
                break;
            default :
                parseloop = false;
                break;
        }
    }

    Instructions instructions;
    if (ilfilename) {
        instructions.from_json_file(ilfilename);
        std::cout << "instructions loaded from json file" << std::endl;
    }

    else if (iquesofilename)
        instructions.from_queso_file(iquesofilename);

    if (concretize)
        instructions.concretize();

    if (dossa)
        instructions.ssa();

    if (forwardslicevarname) {
        Variable trace_var = parseVarString(forwardslicevarname);

        // memory acrobatics
        Instructions new_instructions;
        new_instructions.s_copy_instructions(instructions.slice_forward(trace_var));
        instructions.s_copy_instructions(new_instructions.g_instructions());
    }

    if (backwardslicevarname) {
        Variable trace_var = parseVarString(backwardslicevarname);

        // memory acrobatics
        Instructions new_instructions;
        new_instructions.s_copy_instructions(instructions.slice_backward(trace_var));
        instructions.s_copy_instructions(new_instructions.g_instructions());
    }

    if (smtlib2filename != NULL) {
        std::ofstream smtlib2file;
        smtlib2file.open(smtlib2filename);

        smtlib2file << "(set-option :produce-models true)" << std::endl;
        smtlib2file << "(set-logic QF_AUFBV)" << std::endl;
        smtlib2file << "(set-info :smt-lib-version 2.0)" << std::endl;

        std::list <std::string> declarations = instructions.declarations();
        std::list <std::string> :: iterator it;
        for (it = declarations.begin(); it != declarations.end(); it++) {
            smtlib2file << *it << std::endl;
        }

        std::list <Instruction *> ins = instructions.g_instructions();
        std::list <Instruction *> :: iterator iit;
        for (iit = ins.begin(); iit != ins.end(); iit++) {
            smtlib2file << (*iit)->smtlib2() << std::endl;
        }

        smtlib2file.close();
    }

    if (outputfilename != NULL) {
        std::ofstream outputfile;
        outputfile.open(outputfilename);

        outputfile << instructions.to_json_str();
        outputfile.close();
    }

    if (quesofilename != NULL) {
        std::ofstream quesofile;
        quesofile.open(quesofilename);

        instructions.to_queso().SerializeToOstream(&quesofile);
        quesofile.close();
    }

    return 0;
}