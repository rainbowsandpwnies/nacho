import cherrypy
import ilParser
import os
import subprocess
import tableBuilder
import template
import traceParser
import urllib

RDIS3_DIR = "/home/endeavor/code/rdis3/"
TRACE_DIR = RDIS3_DIR + "data/traces/"
IL_DIR = RDIS3_DIR + "data/ils/"
SMT_DIR = RDIS3_DIR + "data/smtlib2s/"

def link (url, text) :
    return '<a href="' + url + '">' + text + '</a>'

class HelloWorld(object):

    def index(self):

        t = template.Template()

        traces = os.listdir(TRACE_DIR)

        tracesTable = tableBuilder.TableBuilder(['Trace Filename', 'Gen IL', 'View IL'])

        for trace in traces :
            il_text = ''
            if os.path.isfile(IL_DIR + trace + '.il') :
                il_text = link('/dumpil/' + trace + '.il', trace + '.il')
            tracesTable.addRow([link('/dumptrace/' + trace, trace), link('/genil/' + trace, 'gen'), il_text])

        t.setvar('traces', tracesTable.build())

        t.setvar('content', t.parse('start.html'))
        return t.parse('global.html')

    def dumptrace (self, traceFilename) :

        t = template.Template()

        tp = traceParser.TraceParser()
        tp.fromFile(TRACE_DIR + traceFilename)

        tb = tableBuilder.TableBuilder(['address', 'bytes', 'text'])
        for step in tp.steps :
            if 'text' in step :
                tb.addRow(['{0:04x}'.format(step['address']), ''.join(map(lambda x: '{0:02x}'.format(x), step['bytes'])), step['text']])

        t.setvar('content', tb.build())
        return t.parse('global.html')

    def genil (self, traceFilename) :

        t = template.Template()

        proc = subprocess.Popen(RDIS3_DIR + 'src/hsvmtrace ' + TRACE_DIR + traceFilename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout, stderr) = proc.communicate()

        fh = open(IL_DIR + traceFilename + '.il', 'wb')
        fh.write(stdout)
        fh.close()

        t.setvar('content', 'done<br><pre>' + stderr + '</pre>')
        return t.parse('global.html')

    def dumpil (self, ilFilename) :

        t = template.Template()

        ip = ilParser.IlParser()
        ip.fromFile(IL_DIR + ilFilename)

        tb = tableBuilder.TableBuilder(['text'])
        for instruction in ip.instructions :
            text = ip.iltohtml(instruction)
            if text != None :
                tb.addRow([text])

        t.setvar('content', tb.build())
        return t.parse('global.html')



    index.exposed = True
    dumptrace.exposed = True
    genil.exposed = True
    dumpil.exposed = True

cherrypy.config.update({'server.socket_host': '0.0.0.0'})

cherrypy.quickstart(HelloWorld())
