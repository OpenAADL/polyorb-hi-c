#!/usr/bin/python

from xml.dom.minidom import parse
from string import Template
import xml.dom.minidom
#import _cheddar_schedule 
from parser_cheddar_system import clean_cheddar_xml
from parser_cheddar_system import get_task_names
from parser_cheddar_system import get_task_dispatches

#######################
# Parsing Cheddar ADL #
#######################

#clean_cheddar_xml("flight_mgmt_rs_cheddar.xml")
#task_names = get_task_names("flight_mgmt_rs_cheddar.xml")
#task_dispatches = get_task_dispatches("flight_mgmt_rs_cheddar.xml")

######################
# Parsing EventTable #
######################

# Open XML document using minidom parser
DOMTree = xml.dom.minidom.parse("res.xml")
collection = DOMTree.documentElement
if collection.hasAttribute("processor_scheduling"):
   print "Scheduling on processor : %s" % collection.getAttribute("processor_name")

#print "pouet pouet test : %d" % DOMTree.length

# Get all the movies in the collection
global_tag = collection.getElementsByTagName("cheddarKernel_Scheduling")
proc_sched = collection.getElementsByTagName("result")
types_of_events = collection.getElementsByTagName("type_of_event")

start_of_task_capacity_occ = 0

# Print detail of each job dispatch.
for type_of_event in types_of_events:
   if type_of_event.firstChild.data == "START_OF_TASK_CAPACITY":
      #print "*****Time_Unit_Event*****"
      #print ("Type of event: %s" % type_of_event.firstChild.data)
      task_id = type_of_event.parentNode.getElementsByTagName("start_task")[0]
      #print("Task %s is running \n") % task_id.getAttribute("ref")
      start_of_task_capacity_occ += 1
     #getAttribute("ref")

print "Global number of job executions %d" % start_of_task_capacity_occ
fname = 'hyperperriod_config.hh'
with open(fname, 'w') as fout:
    fout.write('#define hyperperiod_size %i' % start_of_task_capacity_occ)
    close(fname)
 #  type = time_unit_event.getElementsByTagName('type')[0]
 #  print "Type: %s" % type.childNodes[0].data
 #  format = time_unit_event.getElementsByTagName('format')[0]
 #  print "Format: %s" % format.childNodes[0].data
 #  rating = time_unit_event.getElementsByTagName('rating')[0]
 #  print "Rating: %s" % rating.childNodes[0].data
 #  description = time_unit_event.getElementsByTagName('description')[0]
 #  print "Description: %s" % description.childNodes[0].data
