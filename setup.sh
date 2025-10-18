#!/usr/bin/env bash

curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y

~/.elan/bin/lean --version

cd /autograder/source

echo "lake update"
~/.elan/bin/lake update 

echo "lake build"
~/.elan/bin/lake build gradescope_lean