#!/bin/bash

name=$1
if   [ "$name" = "clean"   ]; then
    ../../../HOL/bin/Holmake clean; ../../../HOL/bin/Holmake cleanAll
else 
    ../../../HOL/bin/Holmake
fi
