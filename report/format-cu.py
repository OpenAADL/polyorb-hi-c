#!/usr/bin/python

import sys
import re

# init
functions = []
functions_prop = {}
cur_function = ""

data = open("report_po_hi_messages.txt", "r")

# main loop
for line in data:
    # finding function names

    if line.startswith("[rte] annotating function"):
        fun_name = re.search('function (\w+)', line).group(1)
        functions_prop[fun_name] = dict(total=[0, 0], ergo=[0, 0], qed=[0, 0], call=[0, 0], post=[0, 0], assign=[0, 0], loop=[0, 0], assert_rte=[0, 0])
        functions = sorted(functions_prop.keys())
        continue

    # analysing VC proofs

    my_match = re.match('\[wp\] \[(Alt-Ergo|Qed)\] Goal (.*) : (.*)', line)
    if my_match != None:
        prover = 'ergo' if my_match.group(1) == 'Alt-Ergo' else 'qed'
        valid = True if 'Valid' in my_match.group(3) else False

        # finding function name and VC type
        vc_name = my_match.group(2)
        my_fun_match = re.match('(.*)_(call|post|assert_rte|assign|loop).*', vc_name)
        my_fun_pos_name = my_fun_match.group(1)
        vc_type = my_fun_match.group(2)

        for name in functions:
            if re.search(name, my_fun_pos_name) != None:
                fun_name = name
                break

        # updating dictionary
        functions_prop[fun_name][prover][0] = functions_prop[fun_name][prover][0] + 1
        functions_prop[fun_name][vc_type][0] = functions_prop[fun_name][vc_type][0] + 1

        if valid:
            functions_prop[fun_name][prover][1] = functions_prop[fun_name][prover][1] + 1
            functions_prop[fun_name][vc_type][1] = functions_prop[fun_name][vc_type][1] + 1

# close
data.close()
print functions_prop
