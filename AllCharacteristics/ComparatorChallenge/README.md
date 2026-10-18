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

## Successful Comparator run

On **October 17, 2026**, Comparator verified
`CasselsSwinnertonDyerChallenge.rational_point_descent`: statement comparison,
the permitted-axiom check, and Lean's default kernel replay all passed.
The process exited with code 0 after **10,455.5 seconds** (about 2 hours 54 minutes):

```text
Lean default kernel accepts the solution
Your solution is okay!
```

See the [run record](../../verification/evidence/comparator-main-20261017.json)
and [result excerpt](../../verification/evidence/comparator-main-20261017.txt).
The run used native macOS ARM64, Lean v4.33.1, and Comparator revision
`3927ad383f208ae977c340a91c48ac9b497d2097` with additional progress logging.
Nanoda was disabled (`"enable_nanoda": false`, a JSON Boolean).
The `fake-landrun.sh` shim provided no Linux sandbox isolation. The Lean kernel
check was enabled and completed successfully.

## Reproduce the checks

From the repository root, the [verification runner](../../verification/README.md)
builds the solution serially and checks the wider manuscript coverage:

```sh
python3 verification/check.py --run
```

This command performs the manuscript Lean checks; it does not invoke Comparator.
For the separate Comparator command, monitoring, and the native macOS procedure,
see [verification/README.md](../../verification/README.md#comparator).
The configuration remains `AllCharacteristics/ComparatorChallenge/config.json`.
The broader manuscript challenges have larger trusted baselines and remain
`not_run`; the successful run above covers this main CSD challenge only.
