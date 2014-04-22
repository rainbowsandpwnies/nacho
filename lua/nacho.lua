nacho = {}

function nacho.flatten (t)
    function innerFlatten (t, place)
        function shallowCopy (t)
            n = {}
            for k,v in pairs(t) do
                n[k] = v
            end
            return n
        end

        function map (f, t)
            local result = {}
            for k,v in pairs(t) do
                result[k] = f(v)
            end
            return result
        end

        function appendNewReturn (t, v)
            local newTable = shallowCopy(t)
            newTable[#newTable + 1] = v
            return newTable
        end

        if place == 0 then return {{}} end
        -- get results of depth below this depth
        local belowTable = innerFlatten(t, place - 1)

        -- create a new result table
        local result = {}

        -- for every possibility at this level
        for k, possibility in pairs(t[place]) do
            -- for every combo in the below table
            for i, bt in pairs(belowTable) do
                -- append to our result the belowTable with this possibility added to it
                table.insert(result, appendNewReturn(bt, possibility))
            end
        end

        return result
    end
    return innerFlatten(t, #t)
end

function nacho.map (f, t)
    r = {}
    for k,v in pairs(t) do
        r[k] = f(v)
    end
    return r
end

function nacho.iscmp (instruction)
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

function nacho.smtvar (variable)
    if variable.type == 'variable' or variable.type == 'array' then
        return variable.name .. '_' .. tostring(variable.count)
    end
end

function nacho.formatvariable (variable)
    if variable.type == 'variable' or variable.type == 'array' then
        return tostring(variable.bits) .. ':' .. variable.name .. '_' .. tostring(variable.count)
    elseif variable.type == 'constant' then
        return tostring(variable.bits) .. ':' .. variable.lvalhex
    end
end

function nacho.formatinstruction (instruction)
    function quesotext (instruction)
        if instruction.opcode == 'assign' or instruction.opcode == 'signextend' then
            return instruction.opcode
                   .. ' ' .. nacho.formatvariable(instruction.dst)
                   .. ' ' .. nacho.formatvariable(instruction.src)
        elseif instruction.opcode == 'ite' then
            return instruction.opcode
                   .. ' ' .. nacho.formatvariable(instruction.dst)
                   .. ' = ' .. nacho.formatvariable(instruction.condition)
                   .. ' ? ' .. nacho.formatvariable(instruction.t)
                   .. ' : ' .. nacho.formatvariable(instruction.e)
        elseif instruction.opcode == 'store' then
            return instruction.opcode
                   .. ' ' .. nacho.formatvariable(instruction.dstmem)
                   .. '[' .. nacho.formatvariable(instruction.address)
                   .. '] ' .. nacho.formatvariable(instruction.value)
        elseif instruction.opcode == 'load' then
            return instruction.opcode
                   .. ' ' .. nacho.formatvariable(instruction.dst)
                   .. ' ' .. nacho.formatvariable(instruction.mem)
                   .. '[' .. nacho.formatvariable(instruction.address) .. ']'
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
                   .. ' ' .. nacho.formatvariable(instruction.dst)
                   .. ' ' .. nacho.formatvariable(instruction.lhs)
                   .. ' ' .. nacho.formatvariable(instruction.rhs)
        elseif instruction.opcode == 'cmpeq'
            or instruction.opcode == 'cmpltu'
            or instruction.opcode == 'cmpleu'
            or instruction.opcode == 'cmplts'
            or instruction.opcode == 'cmples' then
            return instruction.opcode
                   .. ' ' .. nacho.formatvariable(instruction.dst)
                   .. ' ' .. nacho.formatvariable(instruction.lhs)
                   .. ' ' .. nacho.formatvariable(instruction.rhs)
        elseif instruction.opcode == 'comment' then
            return '; ' .. instruction.comment
        end
    end
    return instruction.pc:string() .. ' ' .. quesotext(instruction)
end

nacho.fmtins = nacho.formatinstruction
nacho.fmtvar = nacho.formatvariable

function nacho.lamesolver (instructions, assertions, values)
    local assertions_text = ''

    for k,ass in pairs(assertions) do
        local asstext = '(assert (= ' .. nacho.smtvar(ass.variable)
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
             .. '(get-value (' .. table.concat(nacho.map(nacho.smtvar, values), ' ') .. '))')
    fh:close()

    local p = io.popen('z3 -smt2 /tmp/smt2')

    text = p:read('*a')

    result = {}
    for identifier,value in string.gmatch(text, '([%a%d_]*) #[xb](%x*)') do
        result[identifier] = tonumber(value, 16)
    end
    return result
end
