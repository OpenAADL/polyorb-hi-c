USER_CFLAGS=-DSIMULATOR -UPOSIX
PO_HI_OBJS += um_threads.o
# The following is specific to ISAE setting, to use SpaceWire
# API. Adapt to your own setting

HOSTNAME:= $(shell hostname)

ifeq ($(HOSTNAME),prise-space-7)
ifeq ($(TARGET),native)
USER_CFLAGS= -I/opt/prise/STAR-Dundee/inc/star
USER_LDFLAGS= -lstar-api -lstar_conf_api_router -lstar_conf_api_mk2
endif
endif
