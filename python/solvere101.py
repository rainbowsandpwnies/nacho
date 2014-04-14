import queso
import subprocess
import re
import sys
import shutil

def smtNum (value, bits) :
    if bits == 1 :
        if value == 0 :
            return '#b0'
        else :
            return '#b1'
    print 'smtNum with value=', value, ' bits=', bits

class Solverre101 :
    def __init__ (self) :
        self.tracedInputs = []
        self.inputVars = ['in0_0', 'in1_0', 'in2_0', 'in3_0', 'in4_0', 'in5_0', 'in6_0', 'in7_0', 'in8_0', 'in9_0']
        self.traceStack = []

    def trace (self, inputBytes) :
        proc = subprocess.Popen('/home/endeavor/code/hsvmtrace/hsvm /home/endeavor/code/hsvmtrace/re101.bin', shell=True, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
        (stdout, stderr) = proc.communicate(''.join(map(lambda x: chr(x), inputBytes)))
        if 'YES' in stdout :
            print 'solution found', inputBytes
            sys.exit(0)
            return None
        return 'trace.json'

    def toQueso (self, inFilename, outFilename) :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/hsvmtrace ' + inFilename, shell=True, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
        (stdout, stderr) = proc.communicate()

        fh = open(outFilename, 'wb')
        fh.write(stdout)
        fh.close()


    # find flags that are influenced by variable
    def findFlags (self, quesoFilename, variable) :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/transform -n ' + quesoFilename + ' -l ' + variable + ' -o /tmp/findFlags', shell=True, stdout=subprocess.PIPE)
        proc.communicate()

        q = queso.Queso()
        q.fromJsonFile('/tmp/findFlags')
        flags = []
        for instruction in q.instructions :
            if isinstance(instruction, queso.InstructionCmp) :
                flags.append(instruction.dst)

        return flags

    # find inputVars that influence var
    def findInputVars (self, quesoFilename, variable) :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/transform -n ' + quesoFilename + ' -b ' + variable.smtlib2() + ' -o /tmp/findInputVars', shell=True, stdout=subprocess.PIPE)
        proc.communicate()

        result = []
        q = queso.Queso()
        q.fromJsonFile('/tmp/findInputVars')
        for instruction in q.instructions :
            for v in instruction.variables_read() :
                if v.smtlib2() in self.inputVars and v.smtlib2() not in result :
                    result.append(v.smtlib2())

        return result


    def solve (self, smt2Filename, assertions, outputs) :
        extrasmt = '\n'.join(map(lambda x: '(assert (= ' + x.smtlib2() + ' ' + smtNum(assertions[x], x.bits), assertions)) + '))'
        extrasmt += '\n(check-sat)\n'
        extrasmt += '(get-value (' + ' '.join(outputs) + '))'

        fh = open(smt2Filename, 'ab')
        fh.write(extrasmt)
        fh.close()

        proc = subprocess.Popen('z3 -smt2 ' + smt2Filename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = proc.communicate()

        results = {}
        matches = re.findall('\((.*?) #x(.*?)\)', stdout)
        for match in matches :
            key = match[0]
            if key[0] == '(' :
                key = key[1:]
            results[key] = int(match[1], 16)
        return results

    def backslicesmt2 (self, quesoFilename, variable, smt2Filename) :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/transform -c -n ' + quesoFilename + ' -b ' + variable + ' -s ' + smt2Filename, shell=True, stdout=subprocess.PIPE)
        proc.communicate()

    def solveFlag (self, inFilename, flag, flagset) :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/transform -n ' + inFilename + ' -l ' + output + ' -s /tmp/solve.smt2', shell=True, stdout=subprocess.PIPE)
        proc.communicate()

        if flagset :
            return

    def mutateInputFromVars (self, inputBytes, inputVars) :
        for i in range(10) :
            varname = 'in' + str(i) + '_0'
            if varname in inputVars :
                inputBytes = inputBytes[0:i] + [inputVars[varname]] + inputBytes[i+1:]
        return inputBytes

    def solveTraceStack (self) :
        while len(self.traceStack) > 0 :
            traceString = self.traceStack[0]
            self.traceStack = self.traceStack[1:]

            print 'tracing', traceString

            self.toQueso(self.trace(traceString), '/tmp/queso')

            print 'finding affected flags'

            flags = []
            # for every input byte, get all flags influenced by those bytes
            for inputVar in self.inputVars :
                tmp = s.findFlags('/tmp/queso', inputVar)
                for t in tmp :
                    if t not in flags :
                        flags.append(t)
            print ', '.join(map(lambda x: x.smtlib2(), flags))
            # for all of the flags, solve for 0 and 1, outputting input bytes
            for flag in flags :
                print 'solving', flag.smtlib2()
                # what input bytes are affected by this flag
                affectedInputBytes = self.findInputVars('/tmp/queso', flag)
                
                self.backslicesmt2('/tmp/queso', flag.smtlib2(), '/tmp/smt2')
                shutil.copyfile('/tmp/smt2', '/tmp/smt2.2')
                flag_0_vars = self.solve('/tmp/smt2', {flag: 0}, affectedInputBytes)
                flag_1_vars = self.solve('/tmp/smt2.2', {flag: 1}, affectedInputBytes)

                for flagvars in [flag_0_vars, flag_1_vars] :
                    print 'flagvars', flag.smtlib2(), flagvars
                    newTraceString = self.mutateInputFromVars(traceString, flag_0_vars)
                    # if this string is not trace, in traceStack or in tracedInputs, add to traceStack
                    if newTraceString != traceString \
                     and newTraceString not in self.traceStack \
                     and newTraceString not in self.tracedInputs :
                        print 'adding', newTraceString
                        self.traceStack.append(newTraceString)

s = Solverre101()
s.traceStack.append([0x41, 0x42, 0x42, 0x41, 0x41, 0x42, 0x41, 0x42, 0x41, 0x41])
s.solveTraceStack()


'''


solveStack = []

s = Sovlerre101()
inputBytes = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
tracefilename = s.trace(inputBytes)
s.toQueso(tracefilename, '/tmp/queso')

# find all flags influenced by input
for inputVar in s.inputVars :
    flags = s.findFlags('/tmp/queso', inputVar)
    for flag in flags :
        proc = subprocess.Popen('/home/endeavor/code/fajita/src/transform -n /tmp/queso -b ' + flag.smtlib2() + ' -s /tmp/smt2', shell=True)
        proc.communicate()

        print s.solve('/tmp/smt2', {flag: 0}, [inputVar])
'''