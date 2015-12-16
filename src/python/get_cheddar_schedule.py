import sys
import subprocess

print "**Converting AADL to Cheddar xml**"

p1 = subprocess.Popen("ocarina -g cheddar -aadlv2 -y  -I\'./\' " + sys.argv[1] ,shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) 

for line in p1.stdout.readlines():
    print line

print "**Computing hyperperiod from Cheddar xml**"
p2 = subprocess.Popen('~/AADLInspectorLinux64b1-4/bin.l64/cheddarkernel -file *cheddar.xml -request bt -xmloutput res.xml', shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

for line in p2.stdout.readlines():
    print line

print "**Computing event table from Cheddar xml**"
p3 = subprocess.Popen('~/AADLInspectorLinux64b1-4/bin.l64/cheddarkernel -file *cheddar.xml -request et -etoutput res.xml', shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

for line in p3.stdout.readlines():
    print line

