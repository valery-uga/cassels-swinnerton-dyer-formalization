import PfaffianDescent.FiniteProjectiveHyperplane

namespace PfaffianDescent
open AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finitely many projective points admit one common degree-one affine chart
over an infinite ground field, even when the ambient scheme has positive dimension. -/
theorem projective_finite_family_avoiding_linear
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {ι : Type*} [Finite ι] (p : ι → ProjectiveSpectrum (grading I)) :
    ∃ z ∈ grading I 1, ∀ a, z ∉ (p a).asHomogeneousIdeal := by
  let bad (a : ι) : Submodule K (grading I 1) :=
    ((p a).asHomogeneousIdeal.toIdeal.restrictScalars K).comap (grading I 1).subtype
  have hbad (a : ι) : bad a ≠ ⊤ := by
    intro ha
    apply (p a).not_irrelevant_le
    change (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤ (p a).asHomogeneousIdeal.toIdeal
    rw [irrelevant_eq_coordinateIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hj : (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) ∈ bad a := by
      rw [ha]
      trivial
    exact hj
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨z, z.2, hz⟩

/-- The image of any finite scheme in a projective polynomial quotient is
contained in one degree-one affine chart over the ground field. -/
theorem finite_scheme_projective_image_avoiding_linear
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f]
    (i : Z ⟶ scheme I) :
    ∃ z ∈ grading I 1, ∀ a : Z, z ∉ (i a).asHomogeneousIdeal := by
  have : IsLocallyArtinian Z := IsLocallyArtinian.of_locallyQuasiFinite f
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : IsArtinianScheme Z := ⟨⟩
  exact projective_finite_family_avoiding_linear I i

end
end PfaffianDescent
