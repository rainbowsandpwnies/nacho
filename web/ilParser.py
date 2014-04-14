import json


class IlParser :
    def __init__ (self) :
        self.instructions = []

    def fromFile (self, filename) :
        fh = open(filename, 'rb')
        jsonRaw = fh.read()
        fh.close()

        self.instructions = json.loads(jsonRaw)

    def ilvartohtml (self, var) :
        if var['type'] == 'VAR' :
            return str(var['bits']) + ':<span style="color: blue;" title="test">' + var['name'] + '_' + str(var['count']) + '</span>'
        elif var['type'] == 'CONST' :
            return str(var['bits']) + ':' + hex(var['lval'])
        elif var['type'] == 'ARRAY' :
            return str(var['bits']) + ':' + str(var['addresses']) + ':<span style="color: blue;">' + str(var['name']) + '_' + str(var['count']) + '</span>'


    def iltohtml (self, il) :
        if il['opcode'] == 'comment' :
            return '<span style="color: green;">; ' + il['comment'] + '</span>'

        elif il['opcode'] == 'add' or il['opcode'] == 'sub' \
          or il['opcode'] == 'xor' or il['opcode'] == 'and' \
          or il['opcode'] == 'shr' or il['opcode'] == 'shl' \
          or il['opcode'] == 'or' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dst']) \
                   + ', ' + self.ilvartohtml(il['lhs']) + ', ' + self.ilvartohtml(il['rhs'])

        elif il['opcode'] == 'store' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dstmem']) + '[' + self.ilvartohtml(il['address']) + '], ' + \
                    self.ilvartohtml(il['value'])

        elif il['opcode'] == 'load' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dst']) + ', ' + self.ilvartohtml(il['mem']) + '[' + self.ilvartohtml(il['address']) + ']'

        elif il['opcode'] == 'assign' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dst']) + ', ' + self.ilvartohtml(il['src'])

        elif il['opcode'] == 'ite' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dst']) + ' = ' + self.ilvartohtml(il['condition']) + ' ? ' + self.ilvartohtml(il['t']) + ' : ' + self.ilvartohtml(il['e'])

        elif il['opcode'] == 'cmpeq' :
            return '<span style="color: red;">' + il['opcode'] + '</span> ' + self.ilvartohtml(il['dst']) + ', ' + self.ilvartohtml(il['lhs']) + ', ' + self.ilvartohtml(il['rhs'])

    def getvars (self, ins) :
        if ins['opcode'] == 'add' or ins['opcode'] == 'sub' \
          or ins['opcode'] == 'xor' or ins['opcode'] == 'and' \
          or ins['opcode'] == 'shr' or ins['opcode'] == 'shl' \
          or ins['opcode'] == 'or' :
            return [ins['dst'], ins['lhs'], ins['rhs']]
        elif ins['opcode'] == 'store' :
            return [ins['dstmem'], ins['srcmem'], ins['address']]
        elif ins['opcode'] == 'load' :
            return [ins['dst'], ins['mem'], ins['address']]
        elif ins['opcode'] == 'assign' :
            return [ins['dst'], ins['src']]
        elif ins['opcode'] == 'ite' :
            return [ins['dst'], ins['condition'], ins['t'], ins['e']]
        elif ins['opcode'] == 'cmpeq' :
            return [ins['dst'], ins['lhs'], ins['rhs']]

    def var_smtlib2_name (ins) :
        if var['type'] == 'VAR' :
            return var['name'] + '_' + str(var['count'])