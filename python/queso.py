import json

VARIABLE, CONSTANT, ARRAY = range(3)

def variableFromJson (j) :
    variable = Variable()
    variable.bits = j['bits']
    variable.count = j['count']

    if j['type'] == 'VAR' :
        variable.type = VARIABLE
        variable.name = j['name']
    elif j['type'] == 'CONST' :
        variable.type = CONSTANT
        variable.lval = j['lval']
    elif j['type'] == 'ARRAY' :
        variable.type = ARRAY
        variable.name = j['name']
        variable.addresses = j['addresses']

    return variable

class Variable :
    def __init__ (self) :
        self.type = -1

    def smtlib2 (self) :
        if self.type == VARIABLE or self.type == ARRAY :
            return self.name + '_' + str(self.count)
        return 'no fuck it'

class Instruction :
    def __init__ (self) :
        pass
    def variables_read (self) :
        return []

class InstructionComment (Instruction) :
    def __init__ (self, comment) :
        self.comment = comment

class InstructionAssign (Instruction) :
    def __init__ (self, dst, src) :
        self.dst = dst
        self.src = src
    def variables_read (self) :
        return [self.src]

class InstructionStore (Instruction) :
    def __init__ (self, dstmem, srcmem, address, value) :
        self.dstmem = dstmem
        self.srcmem = srcmem
        self.address = address
        self.value = value
    def variables_read (self) :
        return [self.srcmem, self.address, self.value]

class InstructionLoad (Instruction) :
    def __init__ (self, mem, address, dst) :
        self.mem = mem
        self.address = address
        self.dst = dst
    def variables_read (self) :
        return [self.mem, self.address]

class InstructionIte (Instruction) :
    def __init__ (self, dst, condition, t, e) :
        self.dst = dst
        self.condition = condition
        self.t = t
        self.e = e
    def variables_read (self) :
        return [self.condition, self.t, self.e]

class InstructionSignExtend (Instruction) :
    def __init__ (self, dst, src) :
        self.dst = dst
        self.src = src
    def variables_read (self) :
        return [self.src]

class InstructionArithmetic (Instruction) :
    def __init__ (self, dst, lhs, rhs) :
        self.dst = dst
        self.lhs = lhs
        self.rhs = rhs

    def variable_written () :
        return self.dst

    def variables_read (self) :
        return [self.lhs, self.rhs]

class InstructionAdd (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'add'

class InstructionSub (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'sub'

class InstructionMul (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'mul'

class InstructionUdiv (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'udiv'

class InstructionUmod (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'umod'

class InstructionAnd (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'and'

class InstructionOr (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'or'

class InstructionXor (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'xor'

class InstructionShr (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'shr'

class InstructionShl (InstructionArithmetic) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionArithmetic.__init__(self, dst, lhs, rhs)
        self.opstring = 'shl'

class InstructionCmp (Instruction) :
    def __init__ (self, dst, lhs, rhs) :
        self.dst = dst
        self.lhs = lhs
        self.rhs = rhs
    def variables_read (self) :
        return [self.lhs, self.rhs]

class InstructionCmpEq (InstructionCmp) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionCmp.__init__(self, dst, lhs, rhs)
        self.opstring = 'cmpeq'

class InstructionCmpLtu (InstructionCmp) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionCmp.__init__(self, dst, lhs, rhs)
        self.opstring = 'cmpeq'

class InstructionCmpLeu (InstructionCmp) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionCmp.__init__(self, dst, lhs, rhs)
        self.opstring = 'cmpeq'

class InstructionCmpLts (InstructionCmp) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionCmp.__init__(self, dst, lhs, rhs)
        self.opstring = 'cmpeq'

class InstructionCmpLes (InstructionCmp) :
    def __init__ (self, dst, lhs, rhs) :
        InstructionCmp.__init__(self, dst, lhs, rhs)
        self.opstring = 'cmpeq'


class Queso :
    def __init__ (self) :
        self.instructions = []

    def fromJsonFile (self, filename) :
        fh = open(filename, 'rb')
        rawJson = fh.read()
        fh.close()

        arithIns = {
            'add': InstructionAdd,
            'sub': InstructionSub,
            'mul': InstructionMul,
            'udiv': InstructionUdiv,
            'umod': InstructionUmod,
            'and': InstructionAnd,
            'or': InstructionOr,
            'xor': InstructionXor,
            'shr': InstructionShr,
            'shl': InstructionShl
        }

        cmpIns = {
            'cmpeq': InstructionCmpEq,
            'cmpltu': InstructionCmpLtu,
            'cmpleu': InstructionCmpLeu,
            'cmplts': InstructionCmpLts,
            'cmples': InstructionCmpLes
        }

        for ins in json.loads(rawJson) :

            if ins['opcode'] == 'comment' :
                self.instructions.append(InstructionComment(ins['comment']))

            elif ins['opcode'] == 'assign' :
                self.instructions.append(InstructionAssign(variableFromJson(ins['dst']), variableFromJson(ins['src'])))

            elif ins['opcode'] == 'store' :
                dstmem = variableFromJson(ins['dstmem'])
                srcmem = variableFromJson(ins['srcmem'])
                address = variableFromJson(ins['address'])
                value = variableFromJson(ins['value'])

                store = InstructionStore(dstmem, srcmem, address, value)

                if ins.has_key('trace_address') :
                    store.trace_address = ins['trace_address']
                self.instructions.append(store)

            elif ins['opcode'] == 'load' :
                mem = variableFromJson(ins['mem'])
                address = variableFromJson(ins['address'])
                dst = variableFromJson(ins['dst'])

                load = InstructionLoad(mem, address, dst)
                if ins.has_key('trace_address') :
                    load.trace_address = ins['trace_address']
                self.instructions.append(load)

            elif ins['opcode'] == 'ite' :
                dst = variableFromJson(ins['dst'])
                condition = variableFromJson(ins['condition'])
                t = variableFromJson(ins['t'])
                e = variableFromJson(ins['e'])
                self.instructions.append(InstructionIte(dst, condition, t, e))

            elif ins['opcode'] == 'signextend' :
                self.instructions.append(InstructionSignExtend(variableFromJson(ins['dst']), variableFromJson(ins['src'])))

            elif ins['opcode'] in arithIns :
                dst = variableFromJson(ins['dst'])
                lhs = variableFromJson(ins['lhs'])
                rhs = variableFromJson(ins['rhs'])
                self.instructions.append(arithIns[ins['opcode']](dst, lhs, rhs))

            elif ins['opcode'] in cmpIns :
                dst = variableFromJson(ins['dst'])
                lhs = variableFromJson(ins['lhs'])
                rhs = variableFromJson(ins['rhs'])
                self.instructions.append(cmpIns[ins['opcode']](dst, lhs, rhs))