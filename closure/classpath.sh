#!/bin/bash

echo `find /home/lganchin/repos/jqf/closure/deps -maxdepth 1 -type f` | sed 's/ /:/g'
