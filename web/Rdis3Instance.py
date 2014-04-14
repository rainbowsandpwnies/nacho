import ilParser
import random
import re
import redis
import subprocess
import time

RDIS3_DIR = "/home/endeavor/code/rdis3/"
TRACE_DIR = RDIS3_DIR + "data/traces/"
IL_DIR = RDIS3_DIR + "data/ils/"
SMT_DIR = RDIS3_DIR + "data/smtlib2s/"

class Rdis3Instance :

    def __init__ (self, instanceName) :
        r = redis.StrictRedis(host='localhost', port=6379, db=0)
        self.instanceName = instanceName
        self.redisInstance = 'instances:' + instanceName

    def setIl (self, ilFilename) :
        r.set(self.redisInstance + ':ilFilename', ilFilename)

    def setVars (self, ilFilename) :
        variables = self.solveForVars(ilFilename)
        for variable in variables :
            r.set(self.redisInstance + ':variables:' + variable, variables[variable])

    def executeSolver (self, smtFilename) :
        print 'executeSolver ' + smtFilename
        proc = subprocess.Popen('scp /tmp/' + smtFilename + ' user@192.168.1.31:/tmp/' + smtFilename, shell=True)
        proc.communicate()

        proc = subprocess.Popen('ssh user@192.168.1.31 z3*/bin/z3 -smt2 /tmp/' + smtFilename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = proc.communicate()

        return stdout

    def solveForVars (self, ilFilename) :
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

rdis3instance = Rdis3Instance ()
vs = rdis3instance.solveForVars('/home/endeavor/code/rdis3/data/ils/0.json.il')
for v in vs :
    print v, vs[v]