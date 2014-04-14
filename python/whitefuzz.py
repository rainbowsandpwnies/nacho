import json
import optparse

parser = optparse.OptionParser()
parser.add_option("-i", "--ilfile", dest="ilfilename", type="string", help="intermediate language file")
parser.add_option("-w", "--wild", help="show wild vars", default=False, action="store_true")
parser.add_option("--opcodes", help="show opcodes", default=False, action="store_true")
parser.add_option("-p", "--print", help="print il", default=False, action="store_true")
parser.add_option("-t", "--traceaddresses", help="print trace addresses", default=False, action="store_true")
parser.add_option("-s", "--show-values", help="show value of comma-seperated vars", dest="showvalues", type="string")
(options, args) = parser.parse_args()

TRACE_ADDRESSES = False
if options.ensure_value('traceaddresses', True) :
    TRACE_ADDRESSES = True

fh = open(options.ilfilename, 'r')
rawjson = fh.read()
fh.close()

il = json.loads(rawjson)

def ilvartostr (var) :
    if var['type'] == 'VAR' :
        return str(var['bits']) + ':' + var['name'] + '_' + str(var['count'])
    elif var['type'] == 'CONST' :
        return str(var['bits']) + ':' + hex(var['lval'])
    elif var['type'] == 'ARRAY' :
        return str(var['bits']) + ':' + str(var['addresses']) + ':' + str(var['name']) + '_' + str(var['count'])


def iltostr (il, noneComment=False) :
    if il['opcode'] == 'comment' :
        if noneComment :
            return None
        return '; ' + il['comment']

    elif il['opcode'] == 'add' or il['opcode'] == 'sub' \
      or il['opcode'] == 'xor' or il['opcode'] == 'and' \
      or il['opcode'] == 'shr' or il['opcode'] == 'shl' \
      or il['opcode'] == 'or' :
        return il['opcode'] + ' ' + ilvartostr(il['dst']) \
               + ', ' + ilvartostr(il['lhs']) + ', ' + ilvartostr(il['rhs'])

    elif il['opcode'] == 'store' :
        if TRACE_ADDRESSES :
            return il['opcode'] + ' ' + ilvartostr(il['dstmem']) + '[' + hex(il['trace_address']) + '], ' + \
                ilvartostr(il['value'])
        else :
            return il['opcode'] + ' ' + ilvartostr(il['dstmem']) + '[' + ilvartostr(il['address']) + '], ' + \
                ilvartostr(il['value'])

    elif il['opcode'] == 'load' :
        if TRACE_ADDRESSES :
            return il['opcode'] + ' ' + ilvartostr(il['dst']) + ', ' + ilvartostr(il['mem']) + '[' + hex(il['trace_address']) + ']'
        else :
            return il['opcode'] + ' ' + ilvartostr(il['dst']) + ', ' + ilvartostr(il['mem']) + '[' + ilvartostr(il['address']) + ']'

    elif il['opcode'] == 'assign' :
        return il['opcode'] + ' ' + ilvartostr(il['dst']) + ', ' + ilvartostr(il['src'])

    elif il['opcode'] == 'ite' :
        return il['opcode'] + ' ' + ilvartostr(il['dst']) + ' = ' + ilvartostr(il['condition']) + ' ? ' + ilvartostr(il['t']) + ' : ' + ilvartostr(il['e'])

    elif il['opcode'] == 'cmpeq' :
        return il['opcode'] + ' ' + ilvartostr(il['dst']) + ', ' + ilvartostr(il['lhs']) + ', ' + ilvartostr(il['rhs'])





if options.ensure_value('opcodes', True) :
    opcodes = []
    for i in il :
        if i['opcode'] not in opcodes :
            opcodes.append(i['opcode'])
    print ' '.join(opcodes)

if options.ensure_value('print', True) :
    for i in il :
        print iltostr(i)

if options.showvalues :
    print options.showvalues