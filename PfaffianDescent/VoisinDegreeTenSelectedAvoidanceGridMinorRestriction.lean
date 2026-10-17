import PfaffianDescent.HomogeneousInterpolationFiniteWitness

/-! Native homogeneous restriction is surjective on the selected monomial
minor open, including at the actual generic ordered chart field. -/
noncomputable section
open MvPolynomial AlgebraicGeometry
open AllCharacteristics.UniversalHomogeneous
namespace PfaffianDescent
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

theorem voisinDegreeTenSelectedAvoidance_restriction_surjective_of_unitMinor
    {K : Type u} [Field K] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → K)
    (hm : IsUnit (homogeneousPointEvaluationMinor m x).det) :
    Function.Surjective (homogeneousSectionRestriction (K := K) (fun j i => x i j) d) := by
  classical
  have hM : IsUnit (homogeneousPointEvaluationMinor m x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hm
  intro z
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM z
  let q : MvPolynomial (Fin 4) K := ∑ j : Fin n, MvPolynomial.monomial (m j).1 (c j)
  have hq : q.IsHomogeneous d := by
    apply IsHomogeneous.sum
    intro j _
    exact isHomogeneous_monomial (c j) (m j).2
  refine ⟨⟨q, hq⟩, ?_⟩
  funext i
  have hi := congrFun hc i
  simpa [homogeneousSectionRestriction_apply, finite_product_evaluation_apply,
    q, homogeneousPointEvaluationMinor, homogeneousPointEvaluationMatrix,
    Matrix.mulVec, dotProduct, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial,
    mul_comm] using hi

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_restriction_surjective_on_minorOpen_fieldPoint
    {R : Type u} [CommRing R] {F : Type v} [Field F] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R)
    (g : Localization.Away (homogeneousMinorDet m x) →+* F) :
    Function.Surjective (homogeneousSectionRestriction (K := F)
      (fun j i => g (algebraMap R (Localization.Away (homogeneousMinorDet m x)) (x i j))) d) := by
  let S := Localization.Away (homogeneousMinorDet m x)
  let y : Fin n → Fin 4 → S := fun i j => algebraMap R S (x i j)
  have hS : IsUnit (homogeneousPointEvaluationMinor m y).det := by
    rw [← homogeneousPointEvaluationMinor_map]
    exact homogeneousMinor_isUnit_on_principalOpen m x
  have hF := hS.map g
  rw [RingHom.map_det, RingHom.mapMatrix_apply,
    homogeneousPointEvaluationMinor_map] at hF
  exact voisinDegreeTenSelectedAvoidance_restriction_surjective_of_unitMinor
    m (fun i j => g (y i j)) hF

end PfaffianDescent
