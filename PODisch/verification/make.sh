#!/bin/bash
export HOLDIR=~/HOL/
name=$1
if   [ "$name" = "clean"   ]; then
    ${HOLDIR}/bin/Holmake clean; ${HOLDIR}/bin/Holmake cleanAll
else 
    ${HOLDIR}/bin/Holmake
fi
