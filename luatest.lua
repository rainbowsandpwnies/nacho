package.cpath = package.cpath .. ";src/?.so"

require("lnacho")

function map (f, t)
    r = {}
    for k,v in pairs(t) do
        r[k] = f(v)
    end
    return r
end

function iscmp (instruction)
    if instruction.opcode == 'cmpeq'
        or instruction.opcode == 'cmpltu'
        or instruction.opcode == 'cmpleu'
        or instruction.opcode == 'cmplts'
        or instruction.opcode == 'cmples' then
        return true
    else
        return false
    end
end

function smtvar (variable)
    if variable.type == 'variable' or variable.type == 'array' then
        return variable.name .. '_' .. tostring(variable.count)
    end
end

function formatvariable (variable)
    if variable.type == 'variable' or variable.type == 'array' then
        return tostring(variable.bits) .. ':' .. variable.name .. '_' .. tostring(variable.count)
    elseif variable.type == 'constant' then
        return tostring(variable.bits) .. ':' .. variable.lvalhex
    end
end

function formatinstruction (instruction)
    if instruction.opcode == 'assign' or instruction.opcode == 'signextend' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dst)
               .. ' ' .. formatvariable(instruction.src)
    elseif instruction.opcode == 'ite' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dst)
               .. ' = ' .. formatvariable(instruction.condition)
               .. ' ? ' .. formatvariable(instruction.t)
               .. ' : ' .. formatvariable(instruction.e)
    elseif instruction.opcode == 'store' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dstmem)
               .. '[' .. formatvariable(instruction.address)
               .. '] ' .. formatvariable(instruction.value)
    elseif instruction.opcode == 'load' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dst)
               .. ' ' .. formatvariable(instruction.mem)
               .. '[' .. formatvariable(instruction.address) .. ']'
    elseif instruction.opcode == 'add'
        or instruction.opcode == 'sub'
        or instruction.opcode == 'mul'
        or instruction.opcode == 'udiv'
        or instruction.opcode == 'umod'
        or instruction.opcode == 'and'
        or instruction.opcode == 'or'
        or instruction.opcode == 'xor'
        or instruction.opcode == 'shr'
        or instruction.opcode == 'shl' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dst)
               .. ' ' .. formatvariable(instruction.lhs)
               .. ' ' .. formatvariable(instruction.rhs)
    elseif instruction.opcode == 'cmpeq'
        or instruction.opcode == 'cmpltu'
        or instruction.opcode == 'cmpleu'
        or instruction.opcode == 'cmplts'
        or instruction.opcode == 'cmples' then
        return instruction.opcode
               .. ' ' .. formatvariable(instruction.dst)
               .. ' ' .. formatvariable(instruction.lhs)
               .. ' ' .. formatvariable(instruction.rhs)
    elseif instruction.opcode == 'comment' then
        return '; ' .. instruction.comment
    end
    return ''
end


function lamesolver (instructions, assertions, values)
    local assertions_text = ''

    for k,ass in pairs(assertions) do
        local asstext = '(assert (= ' .. smtvar(ass.variable)
        if ass.variable.bits == 1 then
            asstext = asstext .. ' #b' .. tostring(ass.value)
        else
            asstext = asstext .. ' #x'
            if ass.variable.bits == 8 then
                asstext = asstext .. string.format('%02x', ass.value)
            elseif ass.variable.bits == 16 then
                asstext = asstext .. string.format('%04x', ass.value)
            elseif ass.variable.bits == 32 then
                asstext = asstext .. string.format('%08x', ass.value)
            elseif ass.variable.bits == 64 then
                asstext = asstext .. string.format('%016x', ass.value)
            end
        end
        asstext = asstext .. '))\n'
        assertions_text = assertions_text .. asstext
    end

    local fh = io.open('/tmp/smt2', 'w')
    fh:write(instructions:smtlib2()
             .. assertions_text
             .. '(check-sat)\n'
             .. '(get-value (' .. table.concat(map(smtvar, values), ' ') .. '))')
    fh:close()

    local p = io.popen('z3 -smt2 /tmp/smt2')

    text = p:read('*a')

    result = {}
    for identifier,value in string.gmatch(text, '([%a%d_]*) #[xb](%x*)') do
        print(identifier, value, tonumber(value, 16))
        result[identifier] = tonumber(value, 16)
    end
    return result
end


function solveVariableFlags (instructions, variable)
    local forwardslice = instructions:slice_forward(variable.name, 0)

    local bitflippers = {}

    for k,instruction in pairs(forwardslice:instructions()) do
        if iscmp(instruction) then
            table.insert(bitflippers, instruction.dst)
            print('-> ' .. formatinstruction(instruction))
        else
            print(formatinstruction(instruction))
        end
    end

    for k,bitflipper in pairs(bitflippers) do
        local backslice = instructions:slice_backward(bitflipper.name, bitflipper.count)
        backslice:concretize()
        backslice:ssa_variable('mem')
        print('\n======' .. formatvariable(bitflipper))
        for k,i in pairs(backslice:instructions()) do print (formatinstruction(i)) end

        local solution0 = lamesolver(backslice, {{variable=bitflipper, value=0}}, {variable})
        local solution1 = lamesolver(backslice, {{variable=bitflipper, value=1}}, {variable})

        print('solution for ' .. formatvariable(bitflipper) .. '=0, ' 
              .. smtvar(variable) .. '=' .. string.format("%x", solution0[smtvar(variable)]))
        print('solution for ' .. formatvariable(bitflipper) .. '=0, ' 
              .. smtvar(variable) .. '=' .. string.format("%x", solution1[smtvar(variable)]))
    end
end

instructions = instructions_t.new()

instructions:from_queso_file("il.queso")

solveVariableFlags(instructions, {type='variable', name='in0', count='0'})