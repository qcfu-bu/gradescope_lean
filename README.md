# Gradescope Lean
A Gradescope autograder for Lean based on [robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main).

## Dependencies
The autograder imports [Mathlib](https://github.com/leanprover-community/mathlib4) is a dependency.
If Mathlib is not needed for the assignment, remove the `[[require]]` section in [lakefile.toml](./lakefile.toml).

## Usage
The autograder expects a `solution.lean` file that acts as a specification for grading. 
The solution file not need to be completed (i.e. proofs can contain `sorry`).

Example `solution.lean`:

```lean
import AutograderLib
import Mathlib.Logic.Basic

@[autogradedProof 10]
theorem problem {a b c: Prop} : a ∧ (a → b) ∧ (b → c) → c := by
  sorry
```

In the solution file, add `import AutograderLib` to the header.
This allow the annotation of theorems with the `autogradedProof <points>` attribute.
Theorems marked by this attribute will be graded and count for `<points>` amount of points.

**Note:**
Assignment files given to students do not need `import AutograderLib` or annotate `autogradedProof`. 

Place the solution file in the [solution](./solution/) directory.

Finally, compress all file using `zip -r autograder.zip ./*` and upload `autograder.zip` to Gradescope.