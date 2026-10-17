# Cassels–Swinnerton-Dyer Comparator challenge

The challenge asks for rational-point descent for a nonzero homogeneous cubic
in four variables over an arbitrary field: a nonzero zero over a finite field
extension of degree coprime to three implies a nonzero zero over the base field.
There is no smoothness, characteristic, perfectness, or separability assumption.
Nonzero coordinate vectors express projective points without introducing a
project-specific definition of a cubic surface.

`Challenge.lean` imports only Mathlib and intentionally contains `sorry`.
`Solution.lean` states the identical theorem and applies the existing internally
proved Coray endpoint. Its proof requires this project's sources and dependencies;
the adapter alone is not a standalone proof distribution. Do not import the two
modules together, because they deliberately declare the same theorem name.
`config.json` permits only `propext`, `Quot.sound`, and `Classical.choice`.

## Installation status (2026-10-15)

Comparator is **not installed** and no Comparator verdict has been obtained.
This machine is macOS ARM64. The installation attempt could not reach GitHub:
`git ls-remote https://github.com/leanprover/comparator.git ...` failed with
`Could not resolve host: github.com`. No `docker`, `colima`, or `limactl` command
was found. The existing project toolchain remains Lean v4.33.1, with Mathlib
v4.33.1; neither was upgraded.

The [official Comparator instructions](https://github.com/leanprover/comparator/blob/master/README.md)
require Landrun, a compatible lean4export, and a Linux sandbox for the supported
verification procedure. Their macOS development workaround uses fake-landrun,
which provides no sandbox; it is not an equivalent installation. Current master
uses Lean v4.35.0 and the repository directs v4.35.0 users to `lake comparator`.
Do not install current master against this v4.33.1 project without resolving that
version mismatch.

To finish installation, use a Linux environment with network access, a compatible
Landlock kernel and a working systemd user session. Follow the upstream build
instructions for Comparator and lean4export at revisions compatible with Lean
v4.33.1, and build Landrun from its upstream main branch. Selection and testing of
these compatible revisions remain outstanding; this document does not claim an
untested revision combination works. Run upstream positive and negative examples
before using the installation to judge this proof. No files have been uploaded.

Once that toolchain is installed, from the `PfaffianDescent` project directory,
with `comparator`, `landrun`, and the compatible `lean4export` on PATH, run:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator AllCharacteristics/ComparatorChallenge/config.json'
```

Use a trusted copy of the challenge, Mathlib, and Lake configuration. For checking
an untrusted submission, use a fresh environment and do not first compile its
solution outside Comparator's sandbox. The existing local proof artifacts are
development evidence, not a substitute for this independent verification.

## Local Lean checks on this Mac

These commands check elaboration and display the solution's transitive axiom
dependencies. They do **not** run Comparator, compare exported environments, or
replay the entire dependency closure in a fresh kernel.
Run from `PfaffianDescent`, sequentially, with fresh log names:

```sh
python3 scripts/cassels_serial_lean_check.py /private/tmp/csd-challenge.log \
  lake env lean -M14000 AllCharacteristics/ComparatorChallenge/Challenge.lean
python3 scripts/cassels_serial_lean_check.py /private/tmp/csd-solution.log \
  lake env lean -M14000 AllCharacteristics/ComparatorChallenge/Solution.lean
cat /private/tmp/csd-challenge.log /private/tmp/csd-solution.log
```

The challenge's placeholder warning is expected. The solution must elaborate
without `sorry` and list only the three permitted axioms. Existing theorem sources,
manuscript files, heartbeat limits, and default Lake targets are unchanged.
