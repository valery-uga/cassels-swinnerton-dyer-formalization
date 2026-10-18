# Manuscript version and formalization scope

The canonical manuscript is **arXiv:2609.15930v3**:
[TeX source](2-proofs.tex) and [PDF](2-proofs.pdf).
Both files were copied unchanged from the supplied `arxiv-v3` directory.
The TeX bytes also match `2-proofs.tex` inside the supplied arXiv source archive.
The PDF identifies itself as v3 and has 16 pages. It was not regenerated from TeX.

| Asset | SHA-256 |
| --- | --- |
| `paper/2-proofs.tex` | `3ba2c489afb164c0a7269d02abe7d23233f1c7dc3d6f85b58d5fec8bca73e299` |
| `paper/2-proofs.pdf` | `dd901a166391585ac9f2e7643dcf9ff4560d8e10df26c2d25125800ca0871f2e` |

The previous manuscript had SHA-256
`93aa0e1fdaa2bdee5a7dbc7fcd786bfdac856a692100da8f016d0dd3e696059e`.
The [coverage table](COVERAGE.md) now uses v3 label locations. All 25 selected
conclusions retain their numbers and labels. Of v3's 27 active numbered
statements, Corollary 1.3 remains excluded and the new Remark 1.5 is outside the
selected scope. The old bibliographic Remark 2.5 is commented out in v3 and is
not counted. Lemma 2.3 retains the perfect-field qualification.

## Changes reviewed

| Change in v3 | Relationship to the Lean formalization |
| --- | --- |
| Theorem 1.4 now states that the Pfaffian of an alternating matrix of linear forms represents zero nontrivially, including an identically zero Pfaffian. | The existing [provider](../AllCharacteristics/TwoProofs.lean#L232) already allows the zero polynomial. Its coefficient matrices encode the linear forms, and its rational section is the projective-point formulation. |
| Lemma 3.3 uses geometric reducedness and expands the Beauville/Buchsbaum–Eisenbud proof. | The existing [provider](../AllCharacteristics/TwoProofs.lean#L244) requires reducedness in the subsection's characteristic-zero setting. The displayed matrix also appears as `frameMatrix` in [FrameMatrix.lean](../PfaffianDescent/FrameMatrix.lean); the actual embedded five-point resolution and presentation are in [ReducedProjectiveFivePoints.lean](../PfaffianDescent/ReducedProjectiveFivePoints.lean). This is not a claim that every added explanatory sentence or the general Buchsbaum–Eisenbud theorem has a separate audited export. |
| Lemma 4.7 expands the semilinear action on the relation space. | The existing [semilinear normalization](../PfaffianDescent/QuarticSemilinearNormalization.lean) and [actual geometric representation](../PfaffianDescent/LiteralArithmeticH0SkewGeometricRepresentation.lean) implement the needed covariance and nonzero-coordinate rescaling. All nine Section 4 conclusions remain applicable. |
| Lemma 5.2 now cites Fogarty for smoothness of the entire relative Hilbert scheme. | In addition to the [global-family lifting theorem](../AllCharacteristics/OriginalGlobalHilbertCubicSubschemeLifting.lean), [originalLiftedCubicGlobalHilbert_smooth_flat001](../PfaffianDescent/OriginalLiftedCubicGlobalHilbertSmooth.lean) now proves smoothness and flatness of the same global Hilbert scheme for every positive length. Its base may be any local Noetherian ring, and the cubic must reduce to a nonzero smooth cubic over its residue field. This includes the manuscript's complete DVR and arbitrary finite flat families, not only closed points of the surface. See the [scope notes](COVERAGE.md#revision-and-method-boundary) and [separate Lean audit](../AllCharacteristics/ManuscriptVerification/GlobalHilbertSmoothness.lean). |
| Proposition 6.3 expands the pushforward formula in `CH_0`. | The project constructs the needed degree-one zero-cycle representative and proves the same final implication. Its `ZeroCycle` objects are cycles before quotienting by rational equivalence; no separate general Chow-group formalization is claimed. |
| New Remark 1.5 discusses del Pezzo surfaces, indices, and quartic counterexamples. | **Not included.** The main cubic theorem is relevant to degree three, but an abstract del Pezzo embedding/index bridge and all of the other cited assertions are not supplied by the selected endpoints. |

## Proof and verification status

The v3 reconciliation preserved the original Cassels–Swinnerton-Dyer Comparator
challenge, solution, and JSON configuration. Subsequently, the main configuration
was set to `"enable_nanoda": false` for the successful native macOS run described
below; the challenge statement and solution proof remain unchanged.
The broader manuscript challenge types and solution
proof bodies are unchanged as well; their Section 4 source-reference comments
now point to v3. Existing proof modules and their pinned Lean/Mathlib versions
are preserved.

The previously recorded 12 audit groups, 63 root checks, and 35 statement-wrapper
checks remain evidence for those unchanged declarations. The v3 reconciliation
adds a source-level mathematical comparison, refreshed source references and
hashes, and regression tests for version checking. It is not a fresh kernel
replay or a Comparator verdict. See the [v3 validation record](../verification/evidence/arxiv-v3.json)
and [verification instructions](../verification/README.md).

That historical v3 record retains the global Hilbert smoothness limitation that
existed at the time. The October 18 proof and verification described below
supersede that limitation; the current coverage is recorded in
[COVERAGE.md](COVERAGE.md#revision-and-method-boundary) and
[coverage.json](../verification/coverage.json).

`python3 verification/check.py` now checks both manuscript assets, active
statement numbering, exact label lines, and an explicit status for every
numbered statement. `python3 verification/check.py --run` performs the full
serial Lean build and dependency audits described in the verification guide.

## Subsequent main-theorem Comparator verification

On October 17, 2026, the main CSD challenge passed statement comparison, the
permitted-axiom check, and Lean default kernel replay, with exit code 0 after
10,455.5 seconds. The [separate run record](../verification/evidence/comparator-main-20261017.json)
and [result excerpt](../verification/evidence/comparator-main-20261017.txt)
document this later verification; the earlier v3 reconciliation record remains
historical evidence for its own checks.

This native macOS ARM64 run used Lean v4.33.1 and Comparator revision `3927ad3`
with progress logging, Nanoda disabled, and `fake-landrun.sh` (no Linux sandbox).
The broader manuscript Comparator configurations remain `not_run`, and all
manuscript scope qualifications above remain in effect.

## Subsequent global Hilbert smoothness verification

The global Hilbert smoothness result is an additional Lean proof with its own
[declaration audit](../AllCharacteristics/ManuscriptVerification/GlobalHilbertSmoothness.lean).
It establishes the cubic case recorded above, without claiming Fogarty's theorem
for arbitrary smooth surfaces. The original main CSD proof is unchanged. This
new result has not been replayed through Comparator and does not change the
scope of the recorded Comparator run.

The October 18, 2026 [verification record](../verification/evidence/global-hilbert-smoothness-20261018.json) records the 76 successful module builds and the three-root audit. The [audit output](../verification/evidence/global-hilbert-smoothness-20261018.txt) prints the precise exported types and their standard axioms.
