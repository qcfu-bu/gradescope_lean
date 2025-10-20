# Gradescope Lean
A Gradescope autograder for [Lean](https://lean-lang.org/) based on [robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main).

## Dependencies
The autograder imports [Mathlib](https://github.com/leanprover-community/mathlib4) as a dependency.
If Mathlib is not needed for the assignment, feel free to remove the `[[require]]` section in [lakefile.toml](./lakefile.toml).

## Usage
The autograder expects a `solution.lean` file that acts as a specification for grading. 
The solution file does not need to be completed (i.e. proofs can contain `sorry`).

Example `solution.lean`:

```lean
import AutograderLib
import Mathlib.Logic.Basic

@[autogradedProof 10]
theorem problem {a b c: Prop} : a ∧ (a → b) ∧ (b → c) → c := by
  sorry
```

In the solution file, add `import AutograderLib` to the header.
This allows the annotation of theorems with the `autogradedProof <points>` attribute.
Theorems marked by this attribute will be graded and count for `<points>` amount of points.

**Note:**
Assignment files given to students do not need to import `AutograderLib` or annotate `autogradedProof`. 

Place the solution file in the [solution](./solution/) directory.

Finally, compress all file using `zip -r autograder.zip ./*` and upload `autograder.zip` to Gradescope.

## Performance Considerations
Due to the large size of Mathlib, you should only get *components* of the Mathlib cache that is depended on
by the assignment. Otherwise, Gradescope might choke when initializing its virtualization for each student submission. 
This is done by modifying `lake exe cache get <Mathlib-component>` in [setup.sh](./setup.sh) to the relevant library.

Example `setup.sh`:

```bash
#!/usr/bin/env bash

cd /autograder/source

curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env

lake exe cache get Mathlib.Data.Real.Basic
lake build gradescope_lean
```

Here, we only get the cache for `Mathlib.Data.Real.Basic`.