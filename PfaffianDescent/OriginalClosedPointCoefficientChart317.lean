import PfaffianDescent.OriginalNormalizedClosedPointChartSeed317
import PfaffianDescent.OriginalFieldCoefficientClassification317
import PfaffianDescent.OriginalCoefficientProjectiveFamily317
import PfaffianDescent.OriginalClassifyingFieldStalk317

/-! The original closed point determines an actual coefficient chart and
field homomorphism whose projective family is exactly that original point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

local instance originalCoefficientClosedPointChartOpen317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {e : ℕ} (hp : p.IsHomogeneous e) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 p hp j

lemma nativeClosedPoint_residueDegree_pos317
    {K : Type u} [Field K] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] (P : closedPoints X) :
    0 < F.residueDegree P.val := by
  letI : Algebra K (X.residueField P.val) := AllCharacteristics.pointAlgebra F P.val
  letI : Module.Finite K (X.residueField P.val) := AllCharacteristics.closedPoint_moduleFinite F P
  rw [← AllCharacteristics.closedPoint_finrank_eq_residueDegree F P]
  exact Module.finrank_pos

variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
  {d : ℕ} (hr : r.IsHomogeneous d) (K : Type u) [Field K] [Algebra R K]
  (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "n" => Scheme.Hom.residueDegree (hypersurfaceToBase (r.map (algebraMap R K))
  (hr.map (algebraMap R K))) P.val

lemma originalClosedPoint_residueDegree_pos317 : 0 < n :=
  @nativeClosedPoint_residueDegree_pos317 K _
    (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (@IsProper.toLocallyOfFiniteType _ _ _
      (isProper_hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K)))) P

variable (j : Fin 4)
  (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
    (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)

include hP in
lemma originalClosedPoint_coefficientChart_exists317 :
    ∃ (i : MonomialCoefficientChartIndex300 3 n)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K),
      (originalCoefficientTestProjectiveFamily317 R n r hr j
        (originalClosedPoint_residueDegree_pos317 R r hr K P) i k).val =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
          P.val).ker := by
  obtain ⟨i, k, hk⟩ := originalFieldPhysicalFamily_coefficientChart_exists317 R r hr j K n
    (originalClosedPoint_residueDegree_pos317 R r hr K P)
    (originalNormalizedClosedPointChartSeed317 R r hr K P j hP)
  refine ⟨i, k, ?_⟩
  exact (congrArg
    (fun Q => (originalNormalizedAffinePointToProjective317
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j n Q).val) hk).trans
        (originalNormalizedClosedPointChartSeed_pushWholeIdeal317 R r hr K P j hP)

include hP in
lemma originalClosedPoint_surjectiveCoefficientChart_exists317
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (i : MonomialCoefficientChartIndex300 3 n)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K),
      Function.Surjective k ∧
      (originalCoefficientTestProjectiveFamily317 R n r hr j
        (originalClosedPoint_residueDegree_pos317 R r hr K P) i k).val =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
          P.val).ker := by
  obtain ⟨i, k, hk⟩ := originalClosedPoint_coefficientChart_exists317 R r hr K P j hP
  exact ⟨i, k, originalClassifyingFieldMap_surjective317 hRK k, hk⟩

end PfaffianDescent
end
