%module po_hi_c_python

%{
#include <deployment.h>
#include <request.h>
#include <activity.h>
#include <po_hi_time.h>
#include <po_hi_task.h>
#include <po_hi_main.h>
#include <po_hi_time.h>
#include <po_hi_types.h>
#include <po_hi_config.h>
#include <po_hi_gqueue.h>
#include <po_hi_transport.h>
%}

%include <types.h>
%include <deployment.h>
%include <po_hi_gqueue.h>
%include <request.h>

