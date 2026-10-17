# Cassels–Swinnerton-Dyer challenge

`Challenge.lean` states rational-point descent for a nonzero homogeneous cubic
in four variables over an arbitrary field. A point over a finite extension of
degree coprime to three implies a point over the base field. There is no
smoothness, characteristic, perfectness, or separability assumption.

The challenge imports only Mathlib and intentionally contains `sorry`.
`Solution.lean` gives the identical statement using the project's internally
proved Coray endpoint. Its dependencies are part of this repository.
`config.json` allows only `propext`, `Quot.sound`, and `Classical.choice`.
Do not import challenge and solution together: they declare the same name.

From the repository root, the [verification runner](../../verification/README.md)
builds the solution serially and checks the wider manuscript coverage:

```sh
python3 verification/check.py --run
```

These Lean checks are not a Comparator verdict. No completed Comparator run is
claimed by this release. The Comparator configuration is
`AllCharacteristics/ComparatorChallenge/config.json`; use a compatible
Lean v4.33.1 installation and the upstream supported sandbox procedure.
See [verification/README.md](../../verification/README.md#comparator) for the
additional challenge configurations and their larger trusted baselines.
