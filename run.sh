#!/bin/bash

# vehicle verify -v Marabou -s pk.vcl -n pk:pk.onnx -c cache -p Ka:5 -p Ke:4 -p Vd:10 -p C_safe:30 -p ttd:2
./verify.sh
vehicle export -t Rocq -c cache -o Rocq/Spec.v -r
make -C ./Rocq -f CoqMakefile
