#!/bin/bash

# To verify a Silver file 'test.sil', run './silicon.sh test.sil'.

set -e

set -e

BASEDIR="$(realpath `dirname $0`)"

CP_FILE="$BASEDIR/silicon_classpath.txt"
LIB_Z3_JAVA="$BASEDIR/libz3java.so"
LIB_Z3="$BASEDIR/libz3.so"

if [ ! -f $CP_FILE ]; then
    (cd $BASEDIR; sbt "export runtime:dependencyClasspath" | tail -n1 > $CP_FILE)
fi

if [ ! -f "$LIB_Z3_JAVA" ]; then
     curl 'http://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/libz3java-4.8.7.so' -o "$LIB_Z3_JAVA"
fi
if [ ! -f "$LIB_Z3" ]; then
     curl 'http://www.sosy-lab.org/ivy/org.sosy_lab/javasmt-solver-z3/libz3-4.8.7.so' -o "$LIB_Z3"
fi

java -Xss30M -Djava.library.path="$(pwd)/" -Dlogback.configurationFile="$BASEDIR/src/main/resources/logback.xml" -cp "`cat $CP_FILE`" viper.silicon.SiliconRunner $@
