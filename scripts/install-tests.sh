#!/bin/bash
# Program: install-tests-sh 
# Purpose: This program executes bondi against the .bon files in the
#          bondi distribution. Note bondi executable must be located
#          in the bondi directory. 
#    Date: 22/05/2009
#  Author: Arun Kumar (arun@it.uts.edu.au)

# ENVIRONMENT VARIABLE PRIMER FOR REFERENCE
# $0 script invoked
# $1, $2, $3 are the command line arguments
# $# Number of command line arguments 
# $@ all command line arguments - white space is preserved
# $* all command line arguments - white space striped 

notImplemented() {
    echo "option $1 is not implemented"
    exit 0
}

isDiff() {
    if diff -q $1 $2 1> /dev/null  
    then
       echo "diff a"
       return 0
    else
       echo "diff b"
       return 1
    fi
}

installDependencies() {
    if [ -d ../scripts ]
    then
        #isDiff ../scripts/configure.in ../$1/configure.in
        cp ../scripts/configure.in ../$1
	cp ../scripts/generate-tests-sh ../$1
	cp ../scripts/run-tests-sh ../$1
    else
        echo "directory [scripts] does not exist"
        echo "This directory contains automake dependencies"
    fi
}

usage() {
    echo "Usage: run-tests-sh [-v -o -l -g -d dirs -fp filepattern]"
    echo "Executes tests using the latest bondi build"
    echo "options:                               "
    echo "    -v print diff output (disabled by default)"
    echo "    -o test files by oldest modification time"
    echo "    -l test files by latest modification time"
    echo "    -g generate .out for bon files"
    echo "    -d set directories"
    echo "    -fp test one or many files eg. customer.bon or *cust*"
    echo "    -h print usage"
    echo "    --help print usage"
    echo "Examples"
    echo "    $ ./run-tests-sh"
    echo "    $ ./run-tests-sh -fp customer*.bon"
    echo "    $ ./run-tests.sh -d \"tests pc_book lib prelude xml\""
    exit 0
}


# all the support options
verbose=false
filepattern="*.bon"
older=no          
younger=no        
generate=no     
DIRS="tests pc_book"

# process command line arguments
while [ $# -gt 0 ]
do
    case "$1" in
        -v)  verbose=true;;
        -o)  notImplemented "-o";; 
        -l)  notImplemented "-l";;
        -g)  notImplemented "-g";;
	-fp) filepattern="$2"; shift;;
	-d)  DIRS="$2"; shift;;
	--help) usage; exit 1;;	
	-h)     usage; exit 1;;	
	-*)     usage; exit 1;;
	*)  break;;	# terminate while loop
    esac
    shift
done

# process each directory
for d in $DIRS; 
do
    echo -n "Entering directory [$d]..."
    if [ -d ../$d ]
    then
        echo "[ok]"	
	cd ../$d
        installDependencies $d
	echo -n "checking automake dependencies in [$d] ..."
	if [ -f generate-tests-sh ] &&
	   [ -f configure.in ]      &&
	   [ -f run-tests-sh ]
	then
	    echo "[ok]"        
	    ./generate-tests-sh -v "$verbose" -fp "$filepattern"
	    cd ../src
	else
	    echo ""        
	    echo "automake dependencies are not installed in [$d]"        
	    echo "directory [$d] does not have configure.in installed"        
	    echo "directory [$d] does not have generate-tests-sh installed"   
	    echo "directory [$d] does not have run-tests-sh installed"        
	fi 
    else
        echo ""
        echo "directory [$d] does not exist"
    fi
done
