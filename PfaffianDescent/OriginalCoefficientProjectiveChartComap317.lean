import PfaffianDescent.OriginalCoefficientProjectiveFamily317

/-! SOURCE ONLY317. Restricting the actual whole projective finite family back
to the SAME normalized chart recovers the entire physical family ideal,
including nilpotents. No projective/affine comparison outcome is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine closed finite composite permits the accepted315 image/comap
identity. IsOpenImmersion supplies the native Mono dictionary abstractly. -/
private theorem originalWholeIdealChartComapCut317
    {Y X : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
    (I : Y.IdealSheafData) [IsClosedImmersion (I.subschemeι ≫ a)]
    (J : X.IdealSheafData) (h : J = I.map a) : J.comap a = I :=
  (congrArg (fun H : X.IdealSheafData => H.comap a) h).trans
    (nativeEmbeddedIdealComapMap315 a I)

/-- For an arbitrary PHYSICAL normalized point, pushing through its actual
original chart then comapping by that SAME embedding recovers the WHOLE
input ideal. Open and closed finite-composite proofs are supplied internally
from accepted312/317 facts; no chart inverse outcome premise is required. -/
lemma originalNormalizedAffinePointToProjective_chartComap317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n) :
    (originalNormalizedAffinePointToProjective317 r hr j n Q).val.comap
        (originalNormalizedHypersurfaceChartEmbedding312 r hr j) = Q.val :=
  @originalWholeIdealChartComapCut317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (hypersurface r hr)
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j)
    Q.val (originalNormalizedAffinePointToProjective_isClosed317 r hr j n Q)
    (originalNormalizedAffinePointToProjective317 r hr j n Q).val
    (originalNormalizedAffinePointToProjective_wholeIdeal317 r hr j n Q)

/-- The ACTUAL original coefficient projective whole family restricts to
its canonical PHYSICAL normalized family on the chosen ORIGINAL chart.
Original ground equation, coefficient AlgHom, rank and whole ideals remain
literal. This is the comparison used after the original square-zero lift. -/
lemma originalCoefficientTestProjectiveFamily_chartComap317
    (R : Type u) [CommRing R] (n : ℕ)
    {B : Type u} [CommRing B] [Algebra R B]
    (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
    (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] B) :
    (originalCoefficientTestProjectiveFamily317 R n r hr j hn i q).val.comap
        (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R B)) (hr.map (algebraMap R B)) j) =
      (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q).val :=
  originalNormalizedAffinePointToProjective_chartComap317
    (r.map (algebraMap R B)) (hr.map (algebraMap R B)) j n
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)

end PfaffianDescent
end
