#!/bin/bash

set -e

# rm -rf cmake* CMake* lib* Testing* tests* include tests compile_commands.json KCBox PreLite Panini ExactMC ExactUS PartialKC
toolname=PSE
if [ $# != 0 ] ; then
	toolname=$1s
fi
# cmake -DCMAKE_BUILD_TYPE=Debug -DENABLE_TESTING=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DTOOLNAME=${toolname} ..
cmake -DSTATICCOMPILE=ON -DENABLE_PYTHON_INTERFACE=ON -DENABLE_TESTING=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DTOOLNAME=${toolname} ..
make -j6
# rm -rf cmake* CMake* lib* Testing* tests* include tests compile_commands.json Makefile

