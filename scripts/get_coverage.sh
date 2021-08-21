#!/bin/bash

# Figure out script absolute path
pushd `dirname $0` > /dev/null
SCRIPT_DIR=`pwd`
popd > /dev/null

ROOT_DIR=`dirname $SCRIPT_DIR`

if [ "$#" -lt 3 ]; then
  echo "Usage: $0 [-i] JACOCO_FILE JACOCO_INCLUDES OUTPUT_DIR" >&2
  exit 1
fi

args=""
if [ "$1" = "-i" ]; then
  args="-i"
  shift 1
fi


export CLASSPATH="$ROOT_DIR/examples/target/classes/,$ROOT_DIR/examples/target/test-classes/"


function join_by { local d=${1-} f=${2-}; if shift 2; then printf %s "$f" "${@/#/$d}"; fi; }


export deps=("$ROOT_DIR/examples/target/dependency/*")
export expandedCP=$(join_by ":" $deps)

if [ -d "$2" ]; then rm -Rf $2; fi
export analyzerJar="$ROOT_DIR/jacoco-jars/static-reachability-1.0-SNAPSHOT.jar"
export jacocoJars="$ROOT_DIR/jacoco-jars/org.jacoco.report-0.8.8.202107100123.jar:$ROOT_DIR/jacoco-jars/org.jacoco.core-0.8.8.202107100123.jar"
export cmd="java -cp $analyzerJar:$jacocoJars edu.neu.ccs.se.reachability.entry.TolerantJacocoReportBuilder $1 $ROOT_DIR/examples/target/classes:$ROOT_DIR/examples/target/test-classes:$expandedCP $2 $3"
echo $cmd
$cmd
