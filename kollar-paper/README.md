# Kollár's unirationality argument: notes on the formalization

Mathematical companion to the Cassels-Swinnerton-Dyer formalization. Prepared October 18, 2026.

[PDF edition](kollar-formalization-notes.pdf) · [Original paper](kollar_math0005146v1.pdf) · [Source information](SOURCES.md) · [Repository overview](../README.md)

## Purpose, version, and scope

János Kollár's *Unirationality of cubic hypersurfaces* proves that a smooth cubic hypersurface of dimension at least two over any field is unirational if and only if it has a rational point. The construction extends the Segre-Manin method to finite fields and arbitrary characteristic. These notes concern **arXiv:math/0005146v1, May 15, 2000**, an eleven-page preprint. Page and result numbers refer to that edition, not the journal edition.

The project formalizes the **smooth cubic-surface case over arbitrary fields**, as needed for Corollary 1.3 of *Two proofs of the Cassels-Swinnerton-Dyer conjecture for cubic surfaces*. This note records the choices made in the Lean formalization of Kollár's arguments, including the explicit constructions and alternative algebraic proofs used.

This is not a formal verification of the entire paper. In particular, the project does not claim its higher-dimensional or singular-hypersurface results, or its separate statements about regular varieties over imperfect fields.

## 1. Characteristic two and smoothness

Lemma 18, p. 9, rules out inseparable projection centers on a smooth cubic in characteristic two. The formalization implements this argument for surfaces without assuming that the field is perfect.

If the relevant partial derivative vanishes identically, the other three partial derivatives are homogeneous quadrics in four variables. Over an algebraic closure, Lean constructs a common nonzero zero using dimension and height arguments. Euler's identity places it on the cubic. This yields a point of the original Jacobian scheme and contradicts smoothness. The resulting separability proof supplies two distinct conjugate residual points on the generic line.

**Lean entry points.** [Euler identity and the smoothness contradiction](../AllCharacteristics/KollarSmoothPartialNonzero.lean), [three homogeneous forms have a common geometric zero](../AllCharacteristics/KollarThreeFormsCommonZero.lean), and [separability of the actual residual quadratic](../AllCharacteristics/KollarCharacteristicTwoActualResidual.lean).

## 2. Parameters, finite fields, and descent

Sections 9-10 of the paper address finite fields by varying the line through the rational point instead of requiring a suitable ground-field line. The formalization follows this principle.

The construction retains independent line parameters and forms the quadratic residual extension explicitly. It constructs the conjugation, the two tangent families, and their secant coordinates. A proved scalar adjustment makes the relevant homogeneous coordinates invariant, after which their coefficients descend to the original parameter field. An actual affine source and rational map over the original ground field complete this step. The final theorem has no field-size, infinitude, or perfectness assumption.

The Lean construction retains redundant affine parameters to simplify these formulas. It therefore proves the existence of a dominant rational map from a finite-dimensional affine space, without asserting that its parameter space has the smallest possible dimension.

**Lean entry points.** [Construction of the descended polynomial family](../AllCharacteristics/KollarNormalizedPolynomialConstruction.lean), [polynomial descent](../AllCharacteristics/UniversalSecantPolynomialDescent.lean), and [identification of the actual affine source](../AllCharacteristics/UniversalAffineSourceIso.lean).

## 3. Genericity and dominance

Proposition 14 and Lemma 15, pp. 7-8, supply the generic tangent-section and secant-dominance arguments. Our surface implementation uses explicit algebraic constructions for the corresponding steps.

To exclude contained lines through the generic residual centers, Lean proves rigidity and descent of the coordinates of a contained line. It then proves that the relevant generic point cannot lie on such a line. Field embeddings and the distinction between constant coefficients and independent parameters are retained throughout. This avoids requiring a separate construction of the complete Fano scheme of lines.

For dominance, the formalization constructs a secant preimage of a generic target. It uses a cubic and a polar quadric, proves the necessary nonvanishing and avoidance conditions, and recovers the target by explicit tangent and secant identities. Homogeneous-relation and function-field arguments then produce an actual dominant rational map. Its dominance is a proved conclusion, not a geometric premise supplied to the final theorem.

**Lean entry points.** [Descent of a contained line's coordinate field](../AllCharacteristics/CubicLineCoordinateFieldDescent.lean), [exclusion of lines through generic points](../AllCharacteristics/SmoothCubicGenericNoContainedLine.lean), [the cubic and polar-quadric construction](../AllCharacteristics/SecantPolarQuadricLift.lean), and [existence of the generic secant preimage](../AllCharacteristics/SmoothCubicGenericSecantPreimage.lean).

## 4. The checked conclusion

The theorem `AllCharacteristics.smoothCubic_unirational_of_rational_section` in [Corollary13Unirationality.lean](../AllCharacteristics/Corollary13Unirationality.lean) proves that a nonzero smooth cubic surface with a rational point is unirational over its original field. Its construction is internal; no Kollár or other unirationality theorem is assumed as an external input.

The definition [IsUnirationalOver](../AllCharacteristics/Unirationality.lean) means that some finite-dimensional affine space has a dominant scheme rational map to the surface, compatible with the structure maps to the ground field. Lemma 11 of the paper discusses the equivalence with using a source of the same dimension as the target. This project's endpoint uses the former convention; it does not separately formalize that dimension-reduction lemma.

Combined with the internally proved Cassels-Swinnerton-Dyer theorem and the converse implication, this gives `AllCharacteristics.twoProofs_corollary13_unirational_iff_zeroCycle_degree_one`: a smooth cubic surface over any field is unirational if and only if it has a zero-cycle of degree one.

All 67 new proof modules and the separate [Unirationality audit](../AllCharacteristics/ManuscriptVerification/Unirationality.lean) passed. The audit checks the actual exported types, allowed axioms, and required construction dependencies; it rejects the older conditional adapters. The [verification record](../verification/evidence/corollary13-unirationality-20261018.json) and [audit output](../verification/evidence/corollary13-unirationality-20261018.txt) document these checks. Existing compiled dependencies were reused; the audit is not an independent replay of every imported proof.

The existing Comparator verification concerns the main Cassels-Swinnerton-Dyer conjecture and is unchanged. No separate Comparator verification of Kollár's result or Corollary 1.3 is claimed.

## References

- J. Kollár, *Unirationality of cubic hypersurfaces*, [arXiv:math/0005146v1](https://arxiv.org/abs/math/0005146v1), May 15, 2000. Published in *Journal of the Institute of Mathematics of Jussieu* **1** (2002), no. 3, pp. 467-476, [DOI: 10.1017/S1474748002000117](https://doi.org/10.1017/S1474748002000117). These notes use the arXiv edition.
- [Manuscript coverage](../paper/COVERAGE.md) and [verification instructions](../verification/README.md).

The Markdown and PDF editions contain the same explanatory text. Source links in the PDF point to the project's GitHub repository; Markdown links resolve within the checkout.
