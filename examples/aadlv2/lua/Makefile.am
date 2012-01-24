LUA_FILES = $(srcdir)/hello.lua $(srcdir)/hello2.lua
AADL_FILES = \
	$(srcdir)/lua-ping.aadl \
	$(srcdir)/lua-simple.aadl

SCENARIO_FILES = \
	$(srcdir)/scenario.aadl \
	$(srcdir)/scenario-ping.aadl 

include $(srcdir)/../../Makefile.common

EXTRA_DIST = $(AADL_FILES) $(SCENARIO_FILES) $(LUA_FILES)

CLEANDIRS = lua_impl lua_ping_local_i
