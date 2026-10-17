# Cassels–Swinnerton-Dyer for cubic surfaces in Lean

This repository contains a Lean formalization of the selected results and methods in **Two proofs of the Cassels–Swinnerton-Dyer conjecture for cubic surfaces**. The [manuscript](paper/2-proofs.tex) and [coverage table](paper/COVERAGE.md) identify the exact scope: 25 selected conclusions across Sections 1–6, including the quadratic-net proof in Section 4, the required internal characteristic-zero Coray reduction, and the global Hilbert-family lifting route in Section 5.

**Corollary 1.3 on unirationality is excluded. Lemma 2.3 is included over perfect fields.** The coverage table records ordinary hypotheses, stronger Lean statements, and differences in proof routes. This is not a formalization of every prose assertion or of the entire 1976 Coray paper.

The main result concerns a nonzero homogeneous cubic in four variables over an arbitrary field. A nontrivial zero over a finite extension of degree coprime to three gives a nontrivial zero over the base field. The selected final endpoints require no external Coray or Voisin theorem as a premise; they include singular and nonreduced cubic hypersurfaces and impose no perfectness or separability assumption on the main theorem.

## Verify the selected manuscript scope

Use the pinned Lean and Mathlib versions in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` (Lean v4.33.1 and Mathlib v4.33.1). Run commands from the repository root.

For source integrity and the coverage inventory, without launching Lean or Lake:

```sh
python3 verification/check.py
```

To build the necessary modules and run the manuscript checks:

```sh
python3 verification/check.py --run
```

The runner builds sequentially, reports progress, and records resumable state. It uses one compiler with a memory guard; a low-memory stop leaves the work available to resume by rerunning the same command. A first run can require substantial time and the pinned dependencies. See [verification/README.md](verification/README.md) for prerequisites, output locations, resumption, and the exact checks performed.

The Lean audit modules print the actual theorem types and axioms, then inspect their transitive type and proof dependencies. They reject axioms outside `propext`, `Quot.sound`, and `Classical.choice`. Additional checks enforce the selected Section 4 independence boundary and the actual global Hilbert-family route. These are Lean elaboration and imported-environment dependency checks; they do not by themselves constitute an independent Comparator verdict or fresh kernel replay of every imported proof.

## Statements and proof entry points

- [Coverage table](paper/COVERAGE.md): every selected manuscript conclusion, full Lean endpoint links, hypotheses, and qualifications.
- [Machine-readable coverage](verification/coverage.json): the same claim inventory, audit roots, exclusions, and Comparator configurations.
- [Internal Coray paper conclusions](AllCharacteristics/InternalCorayPaperConclusions.lean): final endpoints with the characteristic-zero Coray premise supplied internally.
- [Section 4 verification](AllCharacteristics/ManuscriptVerification/SectionFour.lean) and [method checks](AllCharacteristics/ManuscriptVerification/SectionFourMethods1.lean): the independent quadratic-net route and its selected constructions.
- [Global Hilbert integration](AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean) and [route audit](AllCharacteristics/ManuscriptVerification/GlobalHilbertRoute.lean): lifting the original closed subscheme and the positive-characteristic smooth-surface argument.

Some earlier compatibility theorems still expose external theorem or geometric-construction premises. The coverage table selects the internally supplied endpoints and distinguishes them from those adapters. The final manuscript conclusions may use the permitted mixed Chapter 3 route; Section 4 has its own separate independence check.

## Comparator status and trust boundary

The original main-theorem challenge remains at [AllCharacteristics/ComparatorChallenge/Challenge.lean](AllCharacteristics/ComparatorChallenge/Challenge.lean), with its [solution](AllCharacteristics/ComparatorChallenge/Solution.lean) and [configuration](AllCharacteristics/ComparatorChallenge/config.json). Its challenge imports **only Mathlib** and states rational-point descent directly in polynomial coordinates. The solution uses this project's proof. Its [README](AllCharacteristics/ComparatorChallenge/README.md) describes the separate Comparator procedure.

The broader manuscript configurations are [comparator-outside.json](verification/comparator-outside.json) (26 statement wrappers) and [comparator-sectionfour.json](verification/comparator-sectionfour.json) (9 statement wrappers). They have status **`not_run`**: no Comparator verdict is claimed. Their challenge and solution modules deliberately state the same names separately, so they must not be imported together. The challenge placeholders are intentional; the solution modules apply the linked project theorems.

These broader challenge modules import project definitions **and theorem providers**. They therefore trust that whole pinned project baseline, including providers already containing the results. Compiling the solution wrappers checks their explicit statement types against those providers; running Comparator on these configurations would not give them the Mathlib-only independence of the original main-theorem challenge. Source hashes and successful Lean checks are useful evidence, but neither changes this trust boundary or turns `not_run` into a Comparator success.
