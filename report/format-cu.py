#!/usr/bin/python

import sys
import re

# init for pretty print

# define here the report files to be used
latex_file = open("report_" + sys.argv[1] + ".tex", 'w')

# pretty print
def pretty_print():
    pretty_print_latex()

def pretty_print_latex():
    latex_file.write("\\subsection{Proof obligations for \\texttt{" + sys.argv[1].replace('_', '\_') + ".c}}\n\\label{proof:" + sys.argv[1] + "}\n\n")
    latex_file.write("\\begin{longtable}[h]{l l r r r}\n")
    latex_file.write("\\toprule[1.5pt]\n")
    latex_file.write("\multicolumn{1}{c}{\\bfseries Function} & \multicolumn{1}{c}{\\bfseries VC} & \multicolumn{1}{c}{\\bfseries To be proved} & \multicolumn{1}{c}{\\bfseries Proved} & \multicolumn{1}{c}{\\bfseries Time (ms)}\\\\\n")
    latex_file.write("\\midrule\\endhead\n")
    flag = True
    for function in functions:
        if flag:
            flag = False
        else:
            latex_file.write("\\midrule\n")
        latex_file.write("\\nopagebreak\\texttt{" + function.replace('_', '\_') + "} & Total" + pretty_print_row(function, 'total'))
        latex_file.write("\\nopagebreak & Qed" + pretty_print_row(function, 'qed'))
        latex_file.write("\\nopagebreak & Alt-Ergo" + pretty_print_row(function, 'ergo'))
        latex_file.write("\\nopagebreak & Pre" + pretty_print_row(function, 'call'))
        latex_file.write("\\nopagebreak & Post" + pretty_print_row(function, 'post'))
        latex_file.write("\\nopagebreak & RTE" + pretty_print_row(function, 'assert_rte'))
        latex_file.write("\\nopagebreak & Assigns" + pretty_print_row(function, 'assign'))
        latex_file.write("\\nopagebreak & Loop" + pretty_print_row(function, 'loop'))
        latex_file.write("\\nopagebreak & Other" + pretty_print_row(function, 'other'))

    latex_file.write("\\bottomrule[1.5pt]\n")
    latex_file.write("\end{longtable}\n")

def pretty_print_row(function, index):
    if functions_prop[function][index][0] != 0:
        return " & " + str(functions_prop[function][index][0]) + " & " + str(functions_prop[function][index][1]) + " & " + str(functions_prop[function][index][2]) + " \\\\\n"
    else:
         return " & 0 & - & - \\\\\n"

# close for pretty print
def close_pretty_print():
    close_pretty_print_latex()

def close_pretty_print_latex():
    latex_file.close()

# init
functions = []
functions_prop = {}
cur_function = ""

data = open("report_" + sys.argv[1] + ".txt", "r")

# main loop
for line in data:
    # finding function names

    if line.startswith("[rte] annotating function"):
        fun_name = re.search('function (\w+)', line).group(1)
        functions_prop[fun_name] = dict(total=[0, 0, 0], ergo=[0, 0, 0], qed=[0, 0, 0], call=[0, 0, 0], post=[0, 0, 0], assign=[0, 0, 0], loop=[0, 0, 0], assert_rte=[0, 0, 0], other=[0,0,0])
        functions = sorted(functions_prop.keys())
        continue

    # analysing VC proofs

    my_match = re.match('\[wp\] \[(Alt-Ergo|Qed)\] Goal (.*) : (.*)', line)
    if my_match != None:
        prover = 'ergo' if my_match.group(1) == 'Alt-Ergo' else 'qed'

        if 'Valid' in my_match.group(3):
            valid = True
            time_match = re.search('([0-9]*)(m?s)', my_match.group(3))
            if time_match != None:
                time = int(time_match.group(1)) if time_match.group(2) == 'ms' else int(time_match.group(1)) * 1000
            else:
                time = 0
        else:
            valid = False
            time = 0

        # finding function name and VC type
        vc_name = my_match.group(2)
        my_fun_match = re.match('(.*)_(call|post|assert_rte|assign|loop|complete|disjoint).*', vc_name)
        my_fun_pos_name = my_fun_match.group(1)
        vc_type = my_fun_match.group(2)

        if vc_type == 'complete' or vc_type == 'disjoint':
            vc_type = 'other'

        for name in functions:
            if re.search(name, my_fun_pos_name) != None:
                fun_name = name
                break

        # updating dictionary
        functions_prop[fun_name]['total'][0] = functions_prop[fun_name]['total'][0] + 1
        functions_prop[fun_name][prover][0] = functions_prop[fun_name][prover][0] + 1
        functions_prop[fun_name][vc_type][0] = functions_prop[fun_name][vc_type][0] + 1

        if valid:
            functions_prop[fun_name]['total'][1] = functions_prop[fun_name]['total'][1] + 1
            functions_prop[fun_name]['total'][2] = functions_prop[fun_name]['total'][2] + time
            functions_prop[fun_name][prover][1] = functions_prop[fun_name][prover][1] + 1
            functions_prop[fun_name][prover][2] = functions_prop[fun_name][prover][2] + time
            functions_prop[fun_name][vc_type][1] = functions_prop[fun_name][vc_type][1] + 1
            functions_prop[fun_name][vc_type][2] = time

# pretty print
pretty_print()
close_pretty_print()

# close
data.close()
