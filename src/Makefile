OBJS = instruction.o hsvmt.o instructions.o queso.pb.o

CXXFLAGS=-O3 -g -Werror -Wall -std=c++11
INCLUDE=-ljansson -lprotobuf -llua5.1

all : hsvmtrace transform lnacho

hsvmtrace : $(OBJS)
	$(CXX) -o hsvmtrace hsvmtrace.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)
	
transform : $(OBJS)
	$(CXX) -o transform transform.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)

lnacho : $(OBJS)
	$(CXX) -shared -fpic -o lnacho.so lua.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)
	cp lnacho.so ../lua/

%.o : %.cc %.h
	$(CXX) -fpic -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

%.o : %.c %.h
	$(CXX) -fpic -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f hsvmtrace
	rm -f transform
	rm -f lnacho.so
	rm -f ../lua/lnacho.so