##
# Cheddar front-end for trace monitoring module
##

import subprocess
from xml.dom.minidom import parse
from string import Template
import xml.dom.minidom
import os

##
# Compute Cheddar Schedule from AADL specification. Three files are created :
# - 'aadl_spec'_cheddar.xml
# - bt.xml 
# - et.xml
# @param aadl_spec The AADL source file name.

def get_cheddar_schedule(aadl_spec):

    print "**Cleaning old Cheddar xml files**"
    p0 = subprocess.Popen("rm -rf cheddar_xml/ ",shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) 

    print "**Converting AADL to Cheddar xml**"
    p1 = subprocess.Popen("ocarina -g cheddar -aadlv2 -o cheddar_xml -y  -I'./' " + aadl_spec ,shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) 

    for line in p1.stdout.readlines():
        print line

    print "**Looking for Cheddar xml file**"

    
    p4 = subprocess.Popen("find cheddar_xml/ -name '*cheddar.xml'" ,shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) 

    cheddar_xml_file_name = find_cheddar_xml()
    #p4.stdout.readline().rstrip('\n')
    print '' + cheddar_xml_file_name + " has been generated"

    print "**Computing hyperperiod from Cheddar xml**"
    p2 = subprocess.Popen('cheddarkernel -file ' + cheddar_xml_file_name + ' -request bt -xmloutput bt.xml', shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    for line in p2.stdout.readlines():
        print line

    print "**Computing event table from Cheddar xml**"
    p3 = subprocess.Popen('cheddarkernel -file ' + cheddar_xml_file_name + ' -request et -etoutput et.xml', shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    for line in p3.stdout.readlines():
        print line

    return cheddar_xml_file_name

##
# This function has to be called once before using other functions

def clean_cheddar_xml(system_xml):

# Removing file unparsable part
   with open(system_xml, 'r') as fin:
       content = fin.readlines()
   cpt = 0

   for lines in content:
      if lines == "<cheddar>\n" :
         break
      else:
         cpt += 1
      
   file_lenght = len(content)
   with open(system_xml, 'w') as fout:
      for i in range (cpt, len(content)):
         fout.writelines(content[i])
   print ("line number %d" % cpt)


##
# This function prints and returns an array of tasks' names from an Cheddar xml
# file
# @param system_xml The Cheddar xml source file name.

def get_task_names(system_xml):

# Open XML document using minidom parser
   DOMTree = xml.dom.minidom.parse(system_xml)
   collection1 = DOMTree.documentElement


# Get and clean all task identifiers
   tasks = collection1.getElementsByTagName("task")
   task_names = []
   for task in tasks:
      name = task.getElementsByTagName("name")[0]
      name_s = ("%s" % name.firstChild.data)
      name_s = name_s.replace(" ","")
      name_s = name_s.replace("\n","")
      task_names.append(name_s)
   taille = tasks.length
   print ("Tasks number: %d, task names:" % taille)
   for e in task_names:
      print e

   return task_names


def get_task_dispatches(system_xml):

# Open XML document using minidom parser
   DOMTree = xml.dom.minidom.parse(system_xml)
   collection1 = DOMTree.documentElement


# Get all task types
   tasks = collection1.getElementsByTagName("task")
   task_dispatches = []
   for task in tasks:
      task_dispatches.append(task.getAttribute("task_type"))
   taille = tasks.length
   print ("Tasks number: %d, task dispatches:" % taille)
   for e in task_dispatches:
      print e

   return task_dispatches

def parser_cheddar_et():
    # Open XML document using minidom parser
    DOMTree = xml.dom.minidom.parse("./et.xml")
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
    fname = 'hyperperiod_config.hh'
    with open(fname, 'w') as fout:
        fout.write('#define hyperperiod_size %i' % start_of_task_capacity_occ)
        fout.close()
        
        

def find_cheddar_xml():
    for root, dirs, files in os.walk("./"):
        for f in files:
            if "cheddar.xml" in f:
                print f
                return os.path.join(root, f)
