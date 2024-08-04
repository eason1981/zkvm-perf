#!/bin/bash
set -e

rm -f eval/benchmark.csv

nohup python sweep.py &

sleep 1
tail -f nohup.out
