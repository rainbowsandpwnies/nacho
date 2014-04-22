require('lnacho')
require('nacho')


function printins (instructions)
    for k,v in pairs(instructions) do print(nacho.fmtins(v)) end
end

function ite_condition (instructions, condition)
    local result = {}
    for k,instruction in pairs(instructions) do
        if instruction.opcode == 'ite' and
            instruction.condition.name == condition.name and
            instruction.condition.count == condition.count then
            table.insert(result, instruction)
        end
    end
    return result
end


instructions = instructions_t.new()
instructions:from_queso_file(arg[1])

forward_slice = instructions:slice_forward('in0', 0)

print('---- slice_forward in0_0')
printins(instructions:slice_forward('in0', 0):instructions())
print('---- find tmp_193 ite')
printins(ite_condition(instructions:select_opcode('ite'), {name='tmp', count=193}))
--printins(ite_condition(instructions:instructions(), {name='tmp', count=193}))
print('---- slice_backward rip_51')
rip51back = instructions:slice_backward('rip', 51)
printins(rip51back:instructions())


print('---- solve rip_51 tmp_193 == 1')
solutions = nacho.lamesolver(rip51back,
    {{variable={type='variable', name='tmp', count=193, bits=1}, value=1}}, {{name='rip', count=51, type='variable'}})
for k,v in pairs(solutions) do print(k,v) end
print('---- solve rip_51 tmp_193 == 0')

solutions = nacho.lamesolver(rip51back,
    {{variable={type='variable', name='tmp', count=193, bits=1}, value=0}}, {{name='rip', count=51, type='variable'}})
for k,v in pairs(solutions) do print(k,v) end
