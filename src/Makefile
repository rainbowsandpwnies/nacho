OBJS = instruction.o hsvmt.o instructions.o queso.pb.o

CXXFLAGS=-O2 -g -Werror -Wall -std=c++11
INCLUDE=-lcapstone -ljansson -lprotobuf -llua5.1

all : $(OBJS)
	$(CXX) -o hsvmtrace hsvmtrace.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)
	$(CXX) -o transform transform.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)
	$(CXX) -shared -fpic -o lnacho.so lua.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)

%.o : %.cc %.h
	$(CXX) -fpic -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

%.o : %.c %.h
	$(CXX) -fpic -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f test
	rm -f hsvmtrace
	rm -f transform