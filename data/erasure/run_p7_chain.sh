#!/bin/sh
cd "$(dirname "$0")"
export OMP_NUM_THREADS=4
./nfsearch_omp_v2 7 3 161 > raw/nfsearch_p7_E3_n161.txt 2>&1
./nfsearch_omp_v2 7 4 193 > raw/nfsearch_p7_E4_n193.txt 2>&1
