#!/bin/sh
tag=$(echo "$@" | tr " " _)
DUMP=cmp/A_$tag DMAX=13 ./closA "$@" > cmp/A_$tag.out
DUMP=cmp/B_$tag ./walkB 14 "$@" > cmp/B_$tag.out
sort -u cmp/A_$tag > cmp/A_$tag.s; sort -u cmp/B_$tag > cmp/B_$tag.s
if cmp -s cmp/A_$tag.s cmp/B_$tag.s; then eq=SAME; else eq=DIFF; fi
echo "$tag $eq nA=$(wc -l < cmp/A_$tag.s) nB=$(wc -l < cmp/B_$tag.s) | $(cat cmp/A_$tag.out) | $(cat cmp/B_$tag.out)"
rm -f cmp/A_$tag cmp/B_$tag
