#!/bin/bash

conda run -n envp311 vehicle verify -v Marabou -s pk.vcl -n pk:marabou_zero.onnx -c cache -p Ka:4.5 -p Ke:3.5 -p Vd:10 -p C_safe:30 -p ttd:2 -p Ka_over:0.3228 -p Ka_under:0.3227 -p Ke_over:0.415 -p Ke_under:0.4149 -p eps:0.001

# conda run -n envp311 vehicle verify -v Marabou -s pk.vcl -n pk:marabou_zero.onnx -c cache -p Ka:4.5 -p Ke:3.5 -p Vd:10 -p C_safe:30 -p ttd:2 -p Ka_over:0.33 -p Ka_under:0.32 -p Ke_over:0.42 -p Ke_under:0.42
