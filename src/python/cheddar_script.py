import cheddar
import sys

cheddar.get_cheddar_schedule(sys.argv[1]+".aadl")

cheddar.clean_cheddar_xml(sys.argv[1]+"_cheddar.xml")
cheddar.task_names = get_task_names(sys.argv[1]+"_cheddar.xml")
cheddar.task_dispatches = get_task_dispatches(sys.argv[1]++"_cheddar.xml")

cheddar.parser_cheddar_et()
