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

The first Python command checks source hashes, the exact v3 TeX and PDF, statement numbering and line references, and accounting for all 27 active numbered statements (25 included and two excluded). TeX comments are ignored, so the old commented-out remark cannot count as an active statement. It
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
**Its Comparator run passed on October 17, 2026.** Statement comparison,
the permitted-axiom check, and Lean default kernel replay all passed. The process
exited with code 0 after **10,455.5 seconds** (2 hours 54 minutes 15.5 seconds),
and the log ends with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The run exported 110,406 solution declarations. It used a 24 GB ARM64 Mac,
Lean/Mathlib v4.33.1, and Comparator revision
`3927ad383f208ae977c340a91c48ac9b497d2097` with
[progress logging and output flushing](evidence/comparator-progress-20261017.patch).
Those changes did not alter the verification operations. Nanoda was disabled;
Lean's default kernel was enabled. The native `fake-landrun.sh` shim did not
provide Linux sandbox isolation. This is a completed native Comparator check
of the main CSD challenge, not a sandboxed evaluation of an untrusted submission.

See the [run record](evidence/comparator-main-20261017.json),
[result excerpt](evidence/comparator-main-20261017.txt), and
[complete compressed log](evidence/comparator-main-20261017.log.gz).
The record includes hashes, the exact configuration, the observed exit code,
and the distinction between Comparator's log and the guard's terminal output.

Additional explicit statement pairs and configurations remain unrun:

| Configuration | Statements | Comparator status |
|---|---|---|
| `verification/comparator-outside.json` | 26 endpoints supporting the 16 conclusions outside Section 4 | `not_run` |
| `verification/comparator-sectionfour.json` | 9 Section 4 conclusions | `not_run` |

These additional challenges reuse project definitions by importing provider
modules, which also contain proofs. Their trusted baseline therefore includes
those pinned project modules; they are not independent Mathlib-only
reconstructions. Review that baseline before using them as a challenge for an
untrusted submission. The original main challenge has the smaller Mathlib-only
statement baseline.

### Repeat the main check on macOS

Use an already built Comparator installation compatible with Lean v4.33.1;
the revision above is the one used for the recorded run. Finish the guarded
project build first, as described above. Keep the project and Comparator on
their compatible pinned versions. The commands below assume Comparator is
installed at `$HOME/lean-tools/comparator-csd`; change that path if necessary.
Run them from this repository's root. This native procedure is for a trusted
checkout. For sandboxed evaluation, use the supported Linux procedure in the
[Comparator project](https://github.com/leanprover/comparator).

```sh
CSD_COMPARATOR="$HOME/lean-tools/comparator-csd"
CSD_COMPARATOR_LOG="${TMPDIR:-/tmp}/csd-comparator-$(date +%Y%m%d-%H%M%S).log"
export COMPARATOR_LANDRUN="$CSD_COMPARATOR/scripts/fake-landrun.sh"
export COMPARATOR_LEAN4EXPORT="$CSD_COMPARATOR/.lake/packages/lean4export/.lake/build/bin/lean4export"

CSD_GUARD_PROCESS_METRICS=1 python3 verification/serial_guard.py \
  "$CSD_COMPARATOR_LOG" \
  caffeinate -i lake env "$CSD_COMPARATOR/.lake/build/bin/comparator" \
  AllCharacteristics/ComparatorChallenge/config.json
```

The configuration uses `"enable_nanoda": false`: use a JSON Boolean, not the
string `"false"`. `caffeinate -i` prevents idle sleep while the command runs.
The guard uses one Lean thread and prints elapsed time, available memory, swap
activity, and optional CPU/RSS readings about every 15 seconds. In another
terminal, use `tail -f /path/to/the/printed/log` to watch the Comparator log.
The recorded run's extra `STAGE:` messages came from the logging patch; an
unmodified Comparator may buffer its output. CPU activity confirms that the
process is computing, but does not provide a completion percentage.

Allow several hours: the measured 2 hours 54 minutes includes builds using
existing compiled dependencies and is not a time guarantee for another machine
or a clean build. Kernel replay accounted for most of that time. Success requires
the acceptance messages above and a successful exit, not just a successful build
or a `Still running` heartbeat. The guard refuses to overwrite a log; use a new
log name for every attempt. An interrupted Comparator replay starts over on the
next run, although completed project builds can be reused.

For the monitored local Comparator run, `verification/serial_guard.py` stops
below 20% available memory. Sustained system-wide swapping produces warnings
and does not terminate the run. Set `CSD_GUARD_PROCESS_METRICS=1` to report
process-group CPU usage and resident memory; this requires permission to run
`ps`. A shutdown marker still blocks new runs until shutdown is confirmed.
This policy is separate from the conservative serial build runner described
above. A native macOS run using `fake-landrun.sh` does not provide the upstream
Linux sandbox isolation.

## Recorded evidence

[evidence/results.json](evidence/results.json) records the earlier Lean audits,
wrapper checks, and intentional negative tests. Its `comparator: not_run` field
describes that earlier audit session. The [v3 reconciliation record](evidence/arxiv-v3.json)
likewise records no Comparator run in that step. Both records are preserved.
The subsequent successful main CSD run is recorded separately in
[evidence/comparator-main-20261017.json](evidence/comparator-main-20261017.json).
Reproduce the checks yourself rather than treating a committed log as certification.

## arXiv v3 reconciliation

[paper/VERSION.md](../paper/VERSION.md) records the source and PDF hashes and the changes to the coverage map. Existing successful Lean logs are retained as historical evidence for unchanged theorem declarations; they are not relabelled as a new clean-room build or Comparator run. The original main challenge and solution are unchanged; its configuration now disables Nanoda for the native run. The broader challenge types and proof bodies are also unchanged; only their manuscript-reference comments were updated during v3 reconciliation.

The v3 Fogarty global-smoothness assertion and the new del Pezzo Remark 1.5 are explicitly outside the formalized scope. Local smoothness at the original classifier and the named lifting conclusion remain covered.
