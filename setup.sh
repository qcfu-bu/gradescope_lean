#!/usr/bin/env bash

curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env

lean --version

cd /autograder/source

echo "lake update"
lake update

echo "lake build"
lake build gradescope_lean