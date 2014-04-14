import ilParser
import pickle
import random
import re
import shutil
import subprocess
import time

RDIS3_DIR = "/home/endeavor/code/rdis3/"
TRACE_DIR = RDIS3_DIR + "data/traces/"
IL_DIR = RDIS3_DIR + "data/ils/"
SMT_DIR = RDIS3_DIR + "data/smtlib2s/"

class Rdis3 :

    def genTmpFilename (self) :
        return str(time.time()) + str(random.random())

    def solveAssertions (self, ilFilename, assertions) :
        assertionsSmt = '\n'.join(map(lambda a: '(assert (= ' + a + ' ' + assertions[a] + '))', assertions))

        return self.solveForVars(ilFilename, assertionsSmt)

    def executeSolver (self, smtFilename) :
        print 'executeSolver ' + smtFilename
        proc = subprocess.Popen('scp /tmp/' + smtFilename + ' user@192.168.1.31:/tmp/' + smtFilename, shell=True)
        proc.communicate()

        proc = subprocess.Popen('ssh user@192.168.1.31 z3*/bin/z3 -smt2 /tmp/' + smtFilename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = proc.communicate()

        return stdout

    def solveForVars (self, ilFilename, extraSmt='') :
        print 'parsing il'
        ip = ilParser.IlParser()
        ip.fromFile(ilFilename)

        print 'getting variables to solve for'
        variables = []
        for instruction in ip.instructions :
            vs = ip.getvars(instruction)
            if vs == None :
                continue
            for v in vs :
                if v['type'] == 'VAR' :
                    name = str(v['name']) + '_' + str(v['count'])
                    if name not in variables :
                        variables.append(name)

        print 'generating smt2'
        tmpFilename = str(time.time()) + str(random.random()) + '.smt2'

        # create smt2
        proc = subprocess.Popen(RDIS3_DIR + 'src/transform -i ' + ilFilename + ' -s /tmp/' + tmpFilename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        proc.communicate()

        print 'adding smt2 get-values'
        fh = open('/tmp/' + tmpFilename, 'a')
        fh.write(extraSmt)
        fh.write('(check-sat) ')
        fh.write('(get-value (' + '\n'.join(variables) + '))')
        fh.close()

        print 'solving'
        # solve
        output = self.executeSolver(tmpFilename)
        matches = re.findall('\((.*?) #x(.*?)\)', output)

        results = {}
        for match in matches :
            results[match[0]] = int(match[1], 16)
        return results


rdis3 = Rdis3 ()
vs = rdis3.solveAssertions('/home/endeavor/code/rdis3/data/ils/0.json.il', {'in0_0': '#x01'})