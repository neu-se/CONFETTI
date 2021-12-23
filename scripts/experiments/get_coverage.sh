#!/bin/bash

# Figure out script absolute path
pushd `dirname $0` > /dev/null
SCRIPT_DIR=`pwd`
popd > /dev/null

ROOT_DIR=`dirname $SCRIPT_DIR`
ROOT_DIR=`dirname $ROOT_DIR`


if [ "$#" -lt 3 ]; then
  echo "Usage: $0 [-i] JACOCO_FILE JACOCO_INCLUDES OUTPUT_DIR" >&2
  exit 1
fi

args=""
if [ "$1" = "-i" ]; then
  args="-i"
  shift 1
fi

JACOCO_SOURCES=$ROOT_DIR/examples/target/dependency-sources
if [ ! -d $JACOCO_SOURCES ]; then
  (cd $ROOT_DIR/examples && mvn dependency:unpack-dependencies -Dclassifier=sources -DincludeArtifactIds=maven-model,closure-compiler,rhino,ant,bcel -DoutputDirectory=target/dependency-sources)
fi

JACOCO_UTIL_JAR=$ROOT_DIR/target/jacoco-utils-1.0-SNAPSHOT.jar
if [ ! -f $JACOCO_UTIL_JAR ]; then
   mvn -q dependency:get -Dartifact=fun.jvm.jacoco:jacoco-utils:1.0-SNAPSHOT -DremoteRepositories=https://oss.sonatype.org/content/repositories/snapshots
   mvn -q dependency:copy -Dartifact=fun.jvm.jacoco:jacoco-utils:1.0-SNAPSHOT -DoutputDirectory=$ROOT_DIR/target/
fi

export JACOCO_RUNNER_JAR=$ROOT_DIR/target/
export CLASSPATH="$ROOT_DIR/examples/target/test-classes/"

function join_by { local d=${1-} f=${2-}; if shift 2; then printf %s "$f" "${@/#/$d}"; fi; }


export deps=("$ROOT_DIR/examples/target/dependency/*")
export expandedCP=$(join_by ":" $deps)

if [ -d "$2" ]; then rm -Rf $2; fi
export jacocoJars="$ROOT_DIR/examples/target/dependency/org.jacoco.report-0.8.7.jar:$ROOT_DIR/examples/target/dependency/org.jacoco.core-0.8.7.jar"
export cmd="java -cp $JACOCO_UTIL_JAR:$jacocoJars -DJACOCO_SOURCES=$JACOCO_SOURCES fun.jvm.jacoco.reachability.entry.TolerantJacocoReportBuilder $1 $ROOT_DIR/examples/target/test-classes:$expandedCP $2 $3"

COVERAGE_JSON=`$cmd | tail -n 1`
echo $COVERAGE_JSON > jacoco_summary.json
echo $COVERAGE_JSON

