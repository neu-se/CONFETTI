#!/bin/bash
# Figure out script absolute path
pushd `dirname $0` > /dev/null
SCRIPT_DIR=`pwd`
popd > /dev/null

ROOT_DIR=`dirname $SCRIPT_DIR`
ROOT_DIR=`dirname $ROOT_DIR`

if [ "$#" -lt 5 ]; then
  echo "Usage: $0 [-i] CLASS_SUFFIX TEST_METHOD JACOCO_OUTPUT_FILE JACOCO_INCLUDE_GLOB TEST_FILE" >&2
  exit 1
fi

args=""
if [ "$1" = "-i" ]; then
  args="-i"
  shift 1
fi

class="$1"
method="$2"
JACOCO_JAR=$ROOT_DIR/target/jacocoagent.jar
if [ ! -f $JACOCO_JAR ]; then
  mvn -q dependency:copy -Dartifact=org.jacoco:org.jacoco.agent:0.8.7 -DoutputDirectory=$ROOT_DIR/target/
  (cd $ROOT_DIR/target && unzip org.jacoco.agent-0.8.7.jar)
fi

echo $JACOCO_JAR

export CLASSPATH="$ROOT_DIR/examples/target/classes/:$ROOT_DIR/examples/target/test-classes/:$ROOT_DIR/examples/target/dependency/*"
export JVM_OPTS="-javaagent:$JACOCO_JAR=destfile=$3,includes=$4"

"$ROOT_DIR/bin/jqf-repro" $args "$class" "$method" "${@:5}"
echo "$ROOT_DIR/bin/jqf-repro" $args "$class" "$method" "${@:5}"
