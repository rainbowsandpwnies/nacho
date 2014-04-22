package.cpath = package.cpath .. ";src/?.so"

require("lnacho")
require("nacho")


function contains (table, value)
    for k,v in pairs(table) do
        if v == value then return true end
    end
    return false
end


function executeTrace (input)
    fh = io.open('/tmp/input', 'w')
    fh:write(input)
    fh:close()
    local p = io.popen('/home/endeavor/code/hsvmtrace/hsvm /home/endeavor/code/hsvmtrace/re101.bin < /tmp/input')
    local result = p:read('*a')
    p:close()
    os.execute('src/hsvmtrace trace.json > il.queso')
    return result
end


function lamesolver (instructions, assertions, values)
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


-- creates a table of possible values for variable based on backwards solving from
-- flags set by variable in the trace given by instructions
function solveVariableFlags (instructions, variable)
    local forwardslice = instructions:slice_forward(variable.name, 0)

    local bitflippers = {}
    local values = {}

    for k,instruction in pairs(forwardslice:instructions()) do
        if nacho.iscmp(instruction) then
            table.insert(bitflippers, instruction.dst)
        end
    end

    for k,bitflipper in pairs(bitflippers) do
        local backslice = instructions:slice_backward(bitflipper.name, bitflipper.count)
        backslice:concretize()
        backslice:ssa_variable('mem')

        local solution0 = lamesolver(backslice, {{variable=bitflipper, value=0}}, {variable})
        local solution1 = lamesolver(backslice, {{variable=bitflipper, value=1}}, {variable})

        value0 = solution0[nacho.smtvar(variable)]
        value1 = solution1[nacho.smtvar(variable)]

        if contains(values, value0) == false then table.insert(values, value0) end
        if contains(values, value1) == false then table.insert(values, value1) end
    end

    return values
end

-- from a trace, returns a table with the address of the instruction
-- immediately following every ITE instruction
-- the format of the table is address:string() = address
function getConditionalDestinationBlockAddresses (instructions)
    local destinations = {}
    for k,instruction in pairs(instructions) do
        if instruction.opcode == 'ite' then
            if destinations[instructions[k+1].pc:string()] == nil then
                destinations[instructions[k+1].pc:string()] = instructions[k+1].pc
            end
        end
    end
    return destinations
end


function binInput (input)
    return table.concat(nacho.map(string.char, input))
end



destinations = {}

instructions = instructions_t.new()

inputVars = {'in0', 'in1', 'in2', 'in3', 'in4', 'in5', 'in6', 'in7', 'in8', 'in9'}



function traceSolveInput (inputValues) 
    local resultInputs = {}
    print('executing trace')
    if executeTrace(binInput(inputValues)) == 'NO' then
        -- load instructions
        print('loading queso')
        instructions:from_queso_file('il.queso')

        print('find new destinations')
        -- see if we reached any new destinations in this trace
        local traceDestinations = getConditionalDestinationBlockAddresses(instructions:instructions())
        local newDestinations = false
        for addressString,address in pairs(traceDestinations) do
            if destinations[addressString] == nil then
                newDestinations = true
                destinations[addressString] = address
                print('new destination address', address:string())
            end
        end

        -- if there were new destinations, solve for new inputs
        if newDestinations then

            print('slice and solve')
            -- solve for all input variables
            local newInputs = {}
            for varIndex,varName in pairs(inputVars) do
                newInputs[varIndex] = solveVariableFlags(instructions, {type='variable', name=varName, count='0'})
            end

            print('gen new inputs')
            -- create new inputs by mutating off inputValues
            function table.copy (t)
                local newTable = {}
                for k,v in pairs(t) do newTable[k] = v end
                return newTable
            end

            for location,newInput in pairs(newInputs) do
                for k,v in pairs(newInput) do
                    if inputValues[location] ~= v then
                        local resultInput = table.copy(inputValues)
                        resultInput[location] = v
                        table.insert(resultInputs, resultInput)
                    end
                end
            end
        end
    else
        print('result found!')
        print(table.concat(inputValues, ','))
        os.exit(true)
    end
    return resultInputs
end

solvedInputs = {}
inputStack = {{0,0,0,0,0,0,0,0,0,0}}

while #inputStack > 0 do
    local nextInput = inputStack[1]
    table.remove(inputStack, 1)
    table.insert(solvedInputs, table.concat(nextInput, ','))
    print('solving input ' .. table.concat(nextInput, ','))
    local newInputs = traceSolveInput(nextInput)
    for k,newInput in pairs(newInputs) do
        if contains(nacho.map(function (x) return table.concat(x, ',') end, inputStack), table.concat(newInput, ',')) == false 
            and contains(solvedInputs, table.concat(newInput, ',')) == false then
            print('new input', table.concat(newInput, ','))
            table.insert(inputStack, newInput)
        end
    end
end

--[[
for k,input in pairs(inputs) do
    local values = solveVariableFlags(instructions, {type='variable', name=input, count='0'})
    print(input)
    for k,v in pairs(values) do print('\t', v) end
end
]]--