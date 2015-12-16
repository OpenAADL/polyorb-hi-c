#!/usr/bin/python

from xml.dom.minidom import parse
from string import Template
import xml.dom.minidom

#######################
# Parsing Cheddar ADL #
#######################

def clean_cheddar_xml(system_xml):

# This function has to be called once before using other functions
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


