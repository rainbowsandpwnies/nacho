require('lnacho')
require('nacho')

instructions = instructions_t.new()
instructions:from_queso_file(arg[1])

for k,v in pairs(instructions:instructions()) do print(nacho.fmtins(v)) end