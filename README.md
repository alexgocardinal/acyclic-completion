# A nonextendable acyclic edge coloring of K8

This project proves that an explicit proper acyclic edge coloring of K8
with colors 1 through 9 cannot extend to a proper acyclic edge coloring
of K9 while preserving the old edge colors and the palette.

## Main theorem

AcyclicCompletion.certified_counterexample proves properness,
acyclicity, and nonextension of the displayed coloring.

Old vertices are represented by Fin 8. The completed graph uses
Option (Fin 8), with none representing the ninth vertex.
Diagonal entries are zero; actual edges use colors 1 through 9.

The proof uses project-defined encodings of edge colorings and finite
cycles, Lean's standard library, and finite checks proved with decide.
It does not depend on Mathlib.

## Verification

The Lean version is pinned in lean-toolchain.
From the repository directory, run:

    lake build

The build includes the final theorem and prints its axioms.
Its reported dependencies are the standard Lean axioms
propext, Classical.choice, and Quot.sound.

## Proof files

All proof files are in AcyclicCompletion/:

- Witness.lean: matrix, symmetry, palette, and properness.
- Paths.lean: certificates for all 36 pairs of colors.
- Forest.lean: existence of a finite maximum.
- NoCycle.lean: exclusion of cycles embedded in a path.
- Acyclic.lean: cycle definitions and acyclicity.
- Extension.lean: missing colors and forced obstructions.
- Obstructions.lean: the two explicit bichromatic cycles.
- Final.lean: arbitrary completions and the combined theorem.

## Scope

The theorem concerns this explicit K8 coloring and its nonextension.
It does not establish smallest order, historical priority, or
nonextension of the other examples in the research certificate.

The completion question appears in Section 1.2 of:
N. Alon, B. Sudakov, and A. Zaks, "Acyclic Edge Colorings of Graphs,"
Journal of Graph Theory 37 (2001), 157–167.
https://doi.org/10.1002/jgt.1010

## Author

Alex Chan
Harvard University and National Bureau of Economic Research
achan@hbs.edu
