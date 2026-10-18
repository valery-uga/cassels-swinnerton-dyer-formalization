# Cassels–Swinnerton-Dyer for cubic surfaces in Lean

**This project formalizes `2-proofs` and the foundational results it uses from the papers of Coray and Voisin.** It includes Lean proofs of the mathematical statements in [*Two proofs of the Cassels–Swinnerton-Dyer conjecture for cubic surfaces*](paper/2-proofs.pdf), subject to the exceptions below, together with Coray's characteristic-zero degree-1,4,10 reduction and Voisin's degree-ten elimination. The required results from both foundational papers are proved within the project, not assumed as external theorems. The original papers and explanatory notes are in [coray-paper/](coray-paper/) and [voisin-paper/](voisin-paper/); their coverage is limited to the results and constructions needed here, rather than every statement in those papers.

**All numbered mathematical statements in _Two proofs of the Cassels–Swinnerton-Dyer conjecture for cubic surfaces_ have formally checked Lean counterparts, except Corollary 1.3 and Remark 1.5.** This refers to the [arXiv v3 manuscript](paper/2-proofs.tex) ([PDF](paper/2-proofs.pdf)): 25 of its 27 numbered statements are covered, across Sections 1–6. The precise exceptions and the Hilbert-scheme qualification are explained below.

**The two proofs in Sections 3 and 4 have been formalized and checked independently of one another, as explained below.** The Pfaffian argument of Section 3 and the quadratic-net argument of Section 4 are both present; Section 4 is not verified merely by invoking Section 3's conclusion.

**In addition to the Lean verification, the main Cassels–Swinnerton-Dyer theorem passed Comparator on October 17, 2026.** Comparator adds statement comparison, an axiom check, and a fresh Lean-kernel check of the exported solution. The recorded run and its exact safeguards are described below.

The main theorem says that a cubic surface over any field has a rational point if it has a point over a finite extension of degree coprime to three. Equivalently, it has a rational point if it has a zero-cycle of degree one. Singular and nonreduced cubic hypersurfaces are included. The main theorem requires no perfectness or separability assumption, and the final proofs do not assume Coray's or Voisin's results as unproved inputs: the needed reductions are supplied within the formalization.

## What has been checked, and the exceptions

Lean is a proof assistant. A formal proof supplies an exact mathematical statement and a proof that Lean's small kernel checks against its logical rules. This is deductive verification, rather than testing examples or checking numerical evidence. The project uses Mathlib, Lean's mathematical library.

The coverage includes the numbered theorems, propositions, lemmas, and the computational remark on the dimension of H⁰ in Section 4. The [coverage table](paper/COVERAGE.md) matches each covered statement to its Lean theorem, hypotheses, and any differences in formulation. The two excluded numbered statements are:

- **Corollary 1.3:** the equivalence between unirationality of a smooth cubic surface and existence of a zero-cycle of degree one. The rational-point theorem is verified; the further implication from a rational point to unirationality is not included in this coverage.
- **Remark 1.5:** the discussion of other del Pezzo surfaces and comparisons with quartics. These additional comparisons are outside the formalization's scope.

There is also a qualification about a theorem cited inside the proof of **Lemma 5.2**, not an exception to its lifting conclusion. The manuscript invokes Fogarty's theorem to obtain smoothness of the entire relative Hilbert scheme. **Lean checks smoothness at the Hilbert-scheme points corresponding to the closed subschemes being lifted. Global smoothness is unnecessary for this lifting argument and has not been formalized here.** Smoothness at those points, together with the complete henselian base, gives the required lifts; pulling back the actual global universal family then gives the finite flat subschemes. Thus the conclusion of Lemma 5.2 is formally verified using precisely the smoothness needed for it. See the [global Hilbert-family construction](AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean) and [its audit](AllCharacteristics/ManuscriptVerification/GlobalHilbertRoute.lean).

Lemma 2.3 is covered over perfect fields, as stipulated by Section 2 of the paper. Several other Lean statements are stronger than their manuscript counterparts. The coverage claim concerns the mathematical conclusions under the recorded hypotheses, not a line-by-line transcription of every proof sentence, bibliographic assertion, or result in the cited literature. Where a formal proof takes a different route, the coverage table says so. For example, some preliminary point-existence alternatives follow from a stronger descent theorem rather than from the particular residual-point construction printed in the paper. The [version notes](paper/VERSION.md) record the reconciliation with v3.

## The two proofs in Sections 3 and 4

Section 3 uses degree-five cycles and Pfaffian presentations. Section 4 uses a net of quadrics and the tangent-subscheme construction associated with the original degree-four point. Both constructions and their conclusions have Lean proofs.

Their independence means that the two arguments are available separately, while sharing ordinary mathematical foundations and preliminary material. The Section 3 proof providers do not import the Section 4 providers. In the other direction, the [Section 4 audit](AllCharacteristics/ManuscriptVerification/SectionFour.lean) and its six method-audit modules inspect the transitive dependencies of the Section 4 conclusions and constructions and reject the specified Section 3 Pfaffian and degree-five results. This also detects indirect uses of those results through intermediate lemmas.

For a technical reader, the enforced boundary is the explicit list of **17 forbidden Section 3 declarations** in those audits. It is a check of named dependencies in theorem types and proof terms, not a claim that the two developments have disjoint libraries or that software has decided mathematical independence in every possible sense. The later proofs assembling Sections 5 and 6 may use the first route and shared ingredients; the repository does not claim that every final theorem has also been rebuilt through an entirely separate Section 4-only dependency chain.

## The additional Comparator verification

Comparator is an additional verification tool around Lean, rather than a different mathematical foundation. It is reasonable to think of this check as **Lean verification with additional safeguards**. For the main theorem, the successful run performed three checks:

1. **Statement comparison:** the solution was compared with a separately written challenge stating the conjecture directly in polynomial coordinates. The challenge imports only Mathlib, so its statement does not depend on this project's definitions of cubic surfaces or on its theorem providers.
2. **Axiom check:** the proof was checked against the permitted axioms. An admitted proof or an additional axiom asserting a mathematical result would not pass this check.
3. **Kernel replay:** the exported solution was checked again by Lean's default kernel, beyond the earlier project build and declaration audits.

Comparator exited successfully with code 0 after **2 hours 54 minutes 16 seconds**, reporting `Lean default kernel accepts the solution` and `Your solution is okay!`. The [run record](verification/evidence/comparator-main-20261017.json), [result excerpt](verification/evidence/comparator-main-20261017.txt), and [complete compressed log](verification/evidence/comparator-main-20261017.log.gz) preserve the evidence. This additional check covers the main conjecture; it is not being claimed for each of the 25 manuscript conclusions separately.

The run used Lean v4.33.1 on macOS ARM64. **The optional Nanoda checker was disabled, and the native run did not provide Linux sandbox isolation.** The safeguards actually exercised were statement comparison, the permitted-axiom check, and Lean default kernel replay. There is no claim of acceptance by a second kernel implementation or of a sandboxed evaluation of hostile code.

The [challenge](AllCharacteristics/ComparatorChallenge/Challenge.lean), [solution](AllCharacteristics/ComparatorChallenge/Solution.lean), and [configuration](AllCharacteristics/ComparatorChallenge/config.json) remain available at their original paths. The challenge asks whether a nonzero homogeneous cubic in four variables that vanishes nontrivially over a finite extension of degree coprime to three must vanish nontrivially over the base field. The solution applies the project's proof. [Instructions for repeating Comparator](verification/README.md#comparator) are separate from the manuscript's ordinary Lean checks.

## Reproduce the Lean checks

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
- [Notes on Coray's degree reduction](coray-paper/README.md) ([PDF](coray-paper/coray-formalization-notes.pdf)): incidence counts, normalization, multiplicities, and field hypotheses, with links to the formal constructions.
- [Notes on Voisin's degree-ten reduction](voisin-paper/README.md) ([PDF](voisin-paper/voisin-formalization-notes.pdf)): cycle notation, geometric constructions, specialization, and the precise scope of the formalized input.
- Original papers used by the project: [Coray (1976)](coray-paper/coray_1976_algebraic_points.pdf) ([source information](coray-paper/SOURCES.md)) and [Voisin (arXiv v2)](voisin-paper/voisin_2509.17996v2.pdf) ([source information](voisin-paper/SOURCES.md)).
- [Section 4 verification](AllCharacteristics/ManuscriptVerification/SectionFour.lean) and [method checks](AllCharacteristics/ManuscriptVerification/SectionFourMethods1.lean): the independent quadratic-net route and its selected constructions.
- [Global Hilbert integration](AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean) and [route audit](AllCharacteristics/ManuscriptVerification/GlobalHilbertRoute.lean): lifting the original closed subscheme and the positive-characteristic smooth-surface argument.

Some earlier compatibility theorems still expose external theorem or geometric-construction premises. The coverage table selects the internally supplied endpoints and distinguishes them from those adapters. The final manuscript conclusions may use the permitted mixed Chapter 3 route; Section 4 has its own separate independence check.

## Technical scope and trust assumptions

The permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`: propositional extensionality, soundness of quotients, and classical choice. These are standard foundations used by Lean/Mathlib. The audits reject other axioms, including `sorryAx`, which represents an admitted proof. Intentional `sorry` placeholders occur in challenge files; they are not accepted as proofs in the corresponding solutions.

The recorded manuscript validation checked the declarations and their dependencies using existing compiled dependencies; it was not a clean-room rebuild of every dependency. A successful Lean build checks newly compiled proofs, but loading a compiled `.olean` file is not itself fresh kernel replay of every theorem in that file. The subsequent Comparator run adds the recorded replay of the main solution. Exact versions, source hashes, historical audit results, and the later Comparator result are distinguished in [verification/README.md](verification/README.md).

Formal verification establishes the Lean propositions. Reviewing that those propositions faithfully express the intended mathematics remains a human responsibility. The explicit coverage map, the Mathlib-only main challenge, and the published source make that comparison possible; neither a checksum nor a successful log substitutes for it.

The broader manuscript configurations are [comparator-outside.json](verification/comparator-outside.json) (26 statement wrappers) and [comparator-sectionfour.json](verification/comparator-sectionfour.json) (9 statement wrappers). They have status **`not_run`**: no Comparator verdict is claimed. Their challenge and solution modules deliberately state the same names separately, so they must not be imported together. The challenge placeholders are intentional; the solution modules apply the linked project theorems.

These broader challenge modules import project definitions **and theorem providers**. They therefore trust that whole pinned project baseline, including providers already containing the results. Compiling the solution wrappers checks their explicit statement types against those providers; running Comparator on these configurations would not give them the Mathlib-only independence of the original main-theorem challenge. Source hashes and successful Lean checks are useful evidence, but neither changes this trust boundary or turns `not_run` into a Comparator success.

## Coray's and Voisin's papers and companion notes

The formalization also verifies the results from Coray and Voisin needed for the main proof: Coray's degree-1,4,10 reduction for smooth cubic surfaces in characteristic zero, and Voisin's elimination of the degree-ten case by constructing an effective degree-four cycle. These inputs are proved within the Lean development, rather than assumed as external theorems. This verification concerns those required results and constructions, not every statement in either paper.

The original papers used by the project and respectful mathematical notes explaining the formalization are supplied in two directories:

- **[coray-paper/](coray-paper/):** [Coray's original paper](coray-paper/coray_1976_algebraic_points.pdf), companion notes in [Markdown](coray-paper/README.md) and [PDF](coray-paper/coray-formalization-notes.pdf), and [source information](coray-paper/SOURCES.md).
- **[voisin-paper/](voisin-paper/):** [Voisin's paper, arXiv v2](voisin-paper/voisin_2509.17996v2.pdf), companion notes in [Markdown](voisin-paper/README.md) and [PDF](voisin-paper/voisin-formalization-notes.pdf), and [source information](voisin-paper/SOURCES.md).

The notes distinguish notation corrections, arguments requiring further justification, and details made explicit for formal verification. They explain how the relevant constructions are handled in Lean, give references to the original papers, and link to the corresponding proof files. They also identify observations outside the formalized scope.
