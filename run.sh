#!/bin/bash

vehicle verify -v Marabou -s pk.vcl -n pk:pk.onnx -c cache
vehicle export -t Rocq -c cache -o Rocq/Spec.v
make -C ./Rocq -f CoqMakefile
