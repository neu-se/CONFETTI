#!/bin/bash

# Figure out script absolute path
pushd `dirname $0` > /dev/null
SCRIPT_DIR=`pwd`
popd > /dev/null

# The root dir is one up
ROOT_DIR=`dirname $SCRIPT_DIR`

# Create classpath
cp=""

for jar in $SCRIPT_DIR/deps/*.jar; do
  cp="$cp:$jar"
done

echo $cp
