#!/usr/bin/perl




$FUNCTIONS_FILE = "functions-uneeded";
# FUNCTIONS_FILE tell a file which contain all functions name that 
# should not be used

$OBJDUMP_BIN="/usr/bin/objdump";
# The path to objdump program


print $opt_h;
print $opt_f;


#######################################################################
#      DO NOT EDIT AFTER THIS LINE 
#######################################################################

use Getopt::Std;

getopt('fho');

sub usage
{
	print "check-symbols -f dangerous-functions-file binary-file\n";
	print "   -h : print this help\n";
	print "   -f : specify the function file by hand\n";
	print "   -o : specify the objdump binary by hand\n";
}

if( defined $opt_h )
{
	usage;
	exit 0;
}

# We override FUNTION_FILE if -f is provided
$FUNCTIONS_FILE = $opt_f if( defined $opt_f);
$OBJDUMP_BIN = $opt_o if( defined $opt_o);

if(( ! -f $FUNCTIONS_FILE) or ( ! -r $FUNCTIONS_FILE) )
{
	usage;
	print "$FUNCTIONS_FILE does not exists, please check variables\n";
	exit 1;
}

if( $#ARGV != 0 )
{
	usage;
	exit 2;
}
$binary = $ARGV[0];


if(( ! -f $binary) or ( ! -r $binary) )
{
	usage;
	print "$binary does not exists or is not readable\n";
	exit 1;
}

# Do initialisation, will put all function
# name in an array
open FILE , $FUNCTIONS_FILE or die "Cannot open $FUNCTIONS_FILE";
while(<FILE>)
{
	chomp;
	if( ( $_ ne "" ) and ( ! ( /^#.*/ ) ))
	{
		$functions{$_} = 1;
	}
}
close FILE or die "Cannot close $FUNCTIONS_FILE";

print "Ok, will examine file $binary\n";

### Fill @called_functions array which contains all called
### functions in the binary file
open CALL , "$OBJDUMP_BIN -t $binary |" or die "Cannot call $OBJDUMP_BIN";
while (<CALL>)
{
	chomp;
	if( /\*UND\*/ )
	{
		($name) = /[\w\d]+\s+\w\s+[\*\w\d]+\s*[\d\w]+\s+(.+)/;
		push @called_functions , $name;
	}
}
close CALL or die "Cannot close $OBJDUMP_BIN";

$die = 0;
foreach $cf ( @called_functions )
{
  #On native platform, symbols could be declared
  #as symbol@SUFFIX
  #The following line delete the SUFFIX
  $cf =~ s/\@.*//g;
	if( defined( $functions{$cf} ))
	{
		print "Function $cf should not be called\n";
		$die = 1;
	}
}

if( $die == 1 )
{
	printf "Error, dangerous functions are called, please fix your program\n";
	exit 1;
}
else
{
	printf "Success, no dangerous function is called\n";
	exit 0;
}
