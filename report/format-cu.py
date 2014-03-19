#!/usr/bin/python

import sys
import re

# pretty print for CU
def pretty_print_cu(file):
    pretty_print_latex_cu(file)

def pretty_print_latex_cu(file):
    latex_file.write("\\subsection{Proof obligations for \\texttt{" + file.replace('_', '\_') + ".c}}\n\\label{proof:" + file + "}\n\n")
    latex_file.write("\\begin{longtable}[h]{l l r r r r}\n")
    latex_file.write("\\toprule[1.5pt]\n")
    latex_file.write("\multicolumn{1}{l}{\\bfseries Function} & \multicolumn{1}{l}{\\bfseries VC} & \multicolumn{1}{l}{\\bfseries To be proved} & \multicolumn{1}{l}{\\bfseries Proved} & \multicolumn{1}{l}{\\bfseries Time (ms)}\\\\\\endhead\n")
    flag = True
    for function in functions:
        pretty_print_info_latex(functions_prop[function], "\\texttt{" + function.replace('_', '\_') + "}")
    pretty_print_info_latex(total_cu, "\\textbf{Global for CU}")
    latex_file.write("\\bottomrule[1.5pt]\n")
    latex_file.write("\end{longtable}\n")

def pretty_print_info_latex(dic, label):
    #latex_file.write("\\noalign{\\vskip 0.5ex}\\hline\\noalign{\\vskip 0.5ex}\n")
    latex_file.write("\\midrule")
    latex_file.write("\\nopagebreak " + label + " & Qed" + pretty_print_row_latex_cat(dic, 'qed', 2, 'Tool'))
    latex_file.write("\\nopagebreak & Alt-Ergo" + pretty_print_row_latex(dic, 'ergo'))
    latex_file.write("\\nopagebreak \cmidrule{2-6}")
    latex_file.write("\\nopagebreak & Pre" + pretty_print_row_latex_cat(dic, 'call', 6, 'Category'))
    latex_file.write("\\nopagebreak & Post" + pretty_print_row_latex(dic, 'post'))
    latex_file.write("\\nopagebreak & RTE" + pretty_print_row_latex(dic, 'assert_rte'))
    latex_file.write("\\nopagebreak & Assigns" + pretty_print_row_latex(dic, 'assign'))
    latex_file.write("\\nopagebreak & Loop" + pretty_print_row_latex(dic, 'loop'))
    latex_file.write("\\nopagebreak & Other" + pretty_print_row_latex(dic, 'other'))
    latex_file.write("\\nopagebreak \cmidrule{2-6}")
    latex_file.write("\\nopagebreak & Total" + pretty_print_row_latex(dic, 'total'))

def pretty_print_row_latex(dic, index):
    if dic[index][0] != 0:
        return " & " + str(dic[index][0]) + " & " + str(dic[index][1]) + " & " + str(dic[index][2]) + " \\\\\n"
    else:
         return " & 0 & - & - \\\\\n"

def pretty_print_row_latex_cat(dic, index, num, cat):
    if dic[index][0] != 0:
        return " & " + str(dic[index][0]) + " & " + str(dic[index][1]) + " & " + str(dic[index][2]) + "& \\multirow{" + str(num) + "}{*}{\\rotatebox{90}{\\mbox{" + cat + "}}}" + " \\\\\n"
    else:
         return " & 0 & - & - " + "& \\multirow{" + str(num) + "}{*}{\\rotatebox{90}{\\mbox{" + cat + "}}}" + "\\\\\n"

def pretty_print_row_color_latex(dic, index):
    if dic[index][0] != 0:
        return " & \\cellcolor{gray!30}" + str(dic[index][0]) + " & \\cellcolor{gray!30}" + str(dic[index][1]) + " & \\cellcolor{gray!30}" + str(dic[index][2]) + " \\\\\n"
    else:
         return " & \\cellcolor{gray!30} 0 & \\cellcolor{gray!30} - & \\cellcolor{gray!30} - \\\\\n"

# close for pretty print for CU
def close_pretty_print_cu():
    close_pretty_print_latex_cu()

def close_pretty_print_latex_cu():
    latex_file.close()

# pretty print for global stats
def pretty_print_global():
    pretty_print_latex_global()

def pretty_print_latex_global():
    latex_file.write("\\subsection{Global results}\n\\label{proof:global}\n\n")
    latex_file.write("\\begin{longtable}[h]{l r r r r}\n")
    latex_file.write("\\toprule[1.5pt]\n")
    latex_file.write("\multicolumn{1}{l}{\\bfseries VC} & \multicolumn{1}{l}{\\bfseries To be proved} & \multicolumn{1}{l}{\\bfseries Proved} & \multicolumn{1}{l}{\\bfseries Time (ms)}\\\\\\endhead\n")
    #latex_file.write("\\noalign{\\vskip 0.5ex}\\hline\\noalign{\\vskip 0.5ex}\n")
    latex_file.write("\\midrule")
    latex_file.write("\\nopagebreak Qed" + pretty_print_row_latex_cat(total, 'qed', 2, 'Tool'))
    latex_file.write("\\nopagebreak Alt-Ergo" + pretty_print_row_latex(total, 'ergo'))
    latex_file.write("\\midrule")
    latex_file.write("\\nopagebreak Pre" + pretty_print_row_latex_cat(total, 'call', 6, "Category"))
    latex_file.write("\\nopagebreak Post" + pretty_print_row_latex(total, 'post'))
    latex_file.write("\\nopagebreak RTE" + pretty_print_row_latex(total, 'assert_rte'))
    latex_file.write("\\nopagebreak Assigns" + pretty_print_row_latex(total, 'assign'))
    latex_file.write("\\nopagebreak Loop" + pretty_print_row_latex(total, 'loop'))
    latex_file.write("\\nopagebreak Other" + pretty_print_row_latex(total, 'other'))
    latex_file.write("\\midrule")
    latex_file.write("\\nopagebreak Total" + pretty_print_row_latex(total, 'total'))
    latex_file.write("\\bottomrule[1.5pt]\n")
    latex_file.write("\end{longtable}\n")

# close for pretty print for global
def close_pretty_print_global():
    close_pretty_print_latex_global()

def close_pretty_print_latex_global():
    latex_file.close()

# updating function
def update_dictionary(dic):
    dic['total'][0] = dic['total'][0] + 1
    dic[prover][0] = dic[prover][0] + 1
    dic[vc_type][0] = dic[vc_type][0] + 1

    if valid:
        dic['total'][1] = dic['total'][1] + 1
        dic['total'][2] = dic['total'][2] + time
        dic[prover][1] = dic[prover][1] + 1
        dic[prover][2] = dic[prover][2] + time
        dic[vc_type][1] = dic[vc_type][1] + 1
        dic[vc_type][2] = dic[vc_type][2] + time


# main loop
total = dict(total=[0, 0, 0], ergo=[0, 0, 0], qed=[0, 0, 0], call=[0, 0, 0], post=[0, 0, 0], assign=[0, 0, 0], loop=[0, 0, 0], assert_rte=[0, 0, 0], other=[0,0,0])

for c_file in sys.argv[1:]:
    file = c_file.replace('.c', '')
    latex_file = open("report_" + file + ".tex", 'w')

    # init
    functions = []
    functions_prop = {}
    cur_function = ""
    total_cu = dict(total=[0, 0, 0], ergo=[0, 0, 0], qed=[0, 0, 0], call=[0, 0, 0], post=[0, 0, 0], assign=[0, 0, 0], loop=[0, 0, 0], assert_rte=[0, 0, 0], other=[0,0,0])

    data = open("report_" + file + ".txt", "r")

    # main loop for compilation unit
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

            # updating dictionaries
            update_dictionary(functions_prop[fun_name])
            update_dictionary(total_cu)
            update_dictionary(total)

    # pretty print
    pretty_print_cu(file)
    close_pretty_print_cu()

# pretty print global informations
latex_file = open('report_global.tex', 'w')
pretty_print_global()
close_pretty_print_global()

# close
data.close()
