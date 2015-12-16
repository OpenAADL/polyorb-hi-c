#! /usr/bin/python

import cheddar
import sys

generated_file_name = cheddar.get_cheddar_schedule(sys.argv[1])

cheddar.clean_cheddar_xml(generated_file_name)
task_names = cheddar.get_task_names(generated_file_name)
task_dispatches = cheddar.get_task_dispatches(generated_file_name)

cheddar.parser_cheddar_et()
