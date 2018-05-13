#!/bin/bash

# To verify a Silver file 'test.sil', run './silicon.sh test.sil'.

set -e

set -e

BASEDIR="$(realpath `dirname $0`)"

CP_FILE="$BASEDIR/silicon_classpath.txt"

if [ ! -f $CP_FILE ]; then
    (cd $BASEDIR; sbt "export runtime:dependencyClasspath" | tail -n1 > $CP_FILE)
fi

java -Xss30M -Dlogback.configurationFile="$BASEDIR/src/main/resources/logback.xml" -cp "`cat $CP_FILE`" viper.silicon.SiliconRunner $@
