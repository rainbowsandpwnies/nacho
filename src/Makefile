OBJS = instruction.o hsvmt.o instructions.o queso.pb.o

CXXFLAGS=-O2 -g -Werror -Wall -std=c++11
INCLUDE=-lcapstone -ljansson -lprotobuf

all : $(OBJS)
	$(CXX) -o hsvmtrace hsvmtrace.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)
	$(CXX) -o transform transform.cc $(OBJS) $(INCLUDE) $(CXXFLAGS)

%.o : %.cc %.h
	$(CXX) -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

%.o : %.c %.h
	$(CXX) -c -o $@ $< $(INCLUDE) $(CXXFLAGS)

clean :
	rm -f *.o
	rm -f test
	rm -f hsvmtrace
	rm -f transform