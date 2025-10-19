#!/usr/bin/env bash

cd /autograder/source

curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env

lake exe cache get Mathlib.Logic.Basic
lake build gradescope_lean