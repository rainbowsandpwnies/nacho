I give up documenting. No more documenting is going to happen. This project is effectively closed.

nacho
=====

Nacho is a static analysis framework originally designed so endeav0r could do some speaking and talking at aha. However, seeing as how it _is_ a fully-functional static analysis framework, it's worth documenting and releasing to a small group.

The current release includes a translator for hsvm ( http://github.com/endeav0r/hsvm ) but you can bet your ass I'll be writing a translator for x86 in the next few weeks.

Quickstart
==========

You will need libraries for libprotobuf, lua, libmsgpack and jansson


lua-graphviz - libgv-lua
...
apt-get install lua5.1 liblua5.1-dev libmsgpack-dev libjansson-dev libprotobuf-dev
...

You will also need z3. Place the z3 binary in your executable path.

Start by making both hsvmtrace and src. hsvmtrace is a modified version of hsvm that traces execution and dumps to json.

...
make -C hsvmtrace
make -C src
...

now run luatest.lua

...
lua luatest.lua
...

This will begin whitebox fuzzing the re101.bin application with the tracer found in hsvmtrace/hsvm

Queso
===============================

Queso is the name for the IL used by nacho to make decisions, dump to smt, etc. Queso is an RREIL-based IL with embedded trace-specific information. Queso is stored in protobuf format. By storing trace-specific information directly into the IL, we lift our trace to queso and, within queso, maintain all the information we need to make decisions.

Everything in queso has a direct translation to SMT logic.

Queso is still in development. The c++ spec for queso is found entirely within instruction.h.

Queso consists of instructions and variables. All instructions work on, and only on, variables. 

Queso Variables
---------------
There are three types of Variable in queso. They are: VARIABLE, CONSTANT and ARRAY.

Every variable has a bits attribute, which refers to the size (or sort) of the variable. Every variable also has a count attribute, but count is only used with VARIABLE and ARRAY. Count is incremented by nacho when applying Static Single Assignment over a trace.

Variables have the attribute name, which gives the name of

To refer to a variable by its SSA form, use VariableName_Count. For example: eax_214. 
