# Reproducing the manuscript checks

Run from the repository root using the pinned `lean-toolchain` and
`lake-manifest.json`. Python 3.9 or later and Lean's `elan`/`lake` are required.
The runner supports macOS and Linux. Install dependencies using this project's
pinned versions; do not update Mathlib to a different release.

```sh
lake exe cache get
python3 verification/check.py
python3 verification/check.py --run
```

The first Python command checks source hashes and the 25 manuscript labels. It
starts no compiler. The second builds the required local modules in dependency
order, one at a time, then runs the declaration audits again. It prints
`[current/total]`, the active module, log paths, and a message every 15 seconds
while a command is running. Logs and resumable state go in `verification-results/`.
A full first build can take a long time. Rerun the same command to resume after
an interruption; completed modules are retained. Close memory-heavy applications
if the guard stops with less than 45% memory available. The guard also stops on
sustained swapping. It does not guarantee that an operating system can never
run out of memory. Do not run other Lean builds concurrently with this runner.
The `cache get` command downloads external compiled dependencies; it is separate
from the guarded local build.

To check a subset, for example:

```sh
python3 verification/check.py --run --group SectionFour
python3 verification/check.py --run --group Coray --group GlobalHilbertRoute
```

The full run checks 12 groups: the mapped conclusions, the internally proved
Coray result, six groups of Section 4 constructions, and the selected global
Hilbert scheme route. It also builds the original main challenge and the two
additional challenge/solution pairs. Challenge files intentionally use `sorry`;
solution files must not rely on it. Challenge and solution modules deliberately
have identical declaration names and must never be imported together.

## What the checks establish

`coverage.json` gives the manuscript label, Lean endpoint, hypotheses, and scope
qualification for each selected statement. `source-pins.json` records SHA-256
hashes of the local Lean dependency closure and build metadata. These pins detect
changes relative to this release; they are not a signature or proof of provenance.
The readable mapping is [paper/COVERAGE.md](../paper/COVERAGE.md). A human must
still review that each Lean type faithfully expresses its manuscript statement.

The audit prints exported types and axioms, then traverses theorem types, proof
values, projection structure references, recursor rules, and inductive families
in the imported Lean environment. It rejects missing declarations and axioms
outside `propext`, `Quot.sound`, and `Classical.choice` (including `sorryAx`).
Additional checks reject the specified Chapter 3 dependencies for the selected
Section 4/Coray routes. The global Hilbert check requires the actual global-family
producers and excludes earlier local-family substitutes. Its terminal theorem
may retain Chapter 3 dependencies; the intermediate lifting roots may not.
These are precise named-dependency tests, not a general mathematical test of
independence between proofs.

A successful Lean build checks new proofs with Lean's kernel. Dependencies loaded
from `.olean` files are not all independently replayed by the audit. The recorded
validation used existing compiled dependencies, not a new clean-room rebuild.
Use a trusted pinned checkout and caches. The local runner is for this trusted
repository, not a sandbox for hostile submissions.

## Comparator

The original, Mathlib-only statement is in
[AllCharacteristics/ComparatorChallenge](../AllCharacteristics/ComparatorChallenge/README.md).
Additional explicit statement pairs and configurations are:

| Configuration | Statements |
|---|---:|
| `verification/comparator-outside.json` | 26 endpoints supporting the 16 conclusions outside Section 4 |
| `verification/comparator-sectionfour.json` | 9 Section 4 conclusions |

These additional challenges reuse project definitions by importing provider
modules, which also contain proofs. Their trusted baseline therefore includes
those pinned project modules; they are not independent Mathlib-only
reconstructions. Review that baseline before using them as a challenge for an
untrusted submission. The original main challenge has the smaller Mathlib-only
statement baseline.

No Comparator verdict is included in this update. Use a Comparator installation
compatible with this repository's Lean v4.33.1 and the upstream supported sandbox
procedure. Do not assume the current Comparator release supports that toolchain.
After establishing compatibility, pass one of the JSON configurations to
Comparator from this repository root, following the installation's own invocation
instructions. See the [upstream project](https://github.com/leanprover/comparator)
for those instructions. A successful Comparator run and its logs would be
additional evidence; merely compiling the pairs is not a Comparator check.

## Recorded evidence

[evidence/results.json](evidence/results.json) records the checks performed for
this update, with the corresponding text logs. It distinguishes successful checks,
intentional negative tests, and the unperformed Comparator run. Reproduce the
checks yourself rather than treating a committed log as certification.
