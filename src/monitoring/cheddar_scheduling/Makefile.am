################################################################################
# Use of Cheddar with python and C++ compilation rules

clean:
	rm *.o *~ *.cxx cheddar_schedule.py *.so

hyperperiod-cheddar:
	python get_cheddar_schedule.py
	swig -c++ -python cheddar_schedule.i
	c++ -O2 -c -fPIC -std=c++1y cheddar_schedule.cc cheddar_schedule_wrap.cxx -I/usr/include/python2.7/
	gc++ -shared cheddar_schedule.o cheddar_schedule_wrap.o -o _cheddar_schedule.so
	python parser_cheddar_et.py

recompile-cheddar: clean compile-cheddar
