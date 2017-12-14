#!/bin/bash

name=$1
if   [ "$name" = "clean"   ]; then
    /home/hol4/HOL/bin/Holmake clean; /home/hol4/HOL/bin/Holmake cleanAll
elif [ "$name" = "comp" ]; then
    source ../../env.sh; ./compile.sh
else 
    /home/hol4/HOL/bin/Holmake
fi
