###### ASSERTIONS TO CHECK FOR CHEDDAR EVENT TABLE GENERATION



######

bashCommandOcarinaCheddar = "ocarina -aadlv2 -v -y -g cheddar flt_mgmt.aadl"

bashCommandCheddar = "/home/gaudel/AADLInspectorLinux64b1-5/bin.l64/cheddarkernel -file flight_mgmt_rs_cheddar.xml -request et -xmloutput et.xml"




bashCommand = "cwm --rdf test.rdf --ntriples > test.nt"
os.system(bashCommand)


#######


bashCommand = "cwm --rdf test.rdf --ntriples > test.nt"
import subprocess
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output = process.communicate()[0]


#######
