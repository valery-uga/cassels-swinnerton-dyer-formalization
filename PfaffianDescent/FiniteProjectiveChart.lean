import PfaffianDescent.ProjectiveFiniteFamilyHyperplane
import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.NormalizedProjectiveClosedPoint

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any finite closed subscheme of a projective polynomial quotient lies in
one ground-field linear chart, whose ring surjects onto its actual global functions. -/
theorem finite_projective_closed_subscheme_chart
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ z : CoordinateRing I, ∃ hz : z ∈ grading I 1,
      ∃ g : Away (grading I) z →+* Γ(Z, ⊤), Function.Surjective g ∧
        g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
          algebraMap K Γ(Z, ⊤) ∧
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (grading I) z hz (by decide : 0 < 1) = Z.isoSpec.inv ≫ i := by
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨z, hz, hnz⟩ := finite_scheme_projective_image_avoiding_linear I (i ≫ toBase I) i
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I :=
    Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  let q := Z.isoSpec.inv ≫ i
  have hrange : Set.range q ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    change q x ∈ j.opensRange
    change q x ∈ (Proj.awayι (grading I) z hz (by decide : 0 < 1)).opensRange
    rw [Proj.opensRange_awayι]
    exact hnz (Z.isoSpec.inv x)
  let qU := IsOpenImmersion.lift j q hrange
  have hU : qU ≫ j = q := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (qU ≫ j) := hU.symm ▸ inferInstanceAs (IsClosedImmersion q)
  have : IsClosedImmersion qU := IsClosedImmersion.of_comp qU j
  let g := (Spec.preimage qU).hom
  have hg : Spec.map (CommRingCat.ofHom g) = qU := Spec.map_preimage qU
  have hj : j ≫ toBase I = Spec.map
      (CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) := by
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
      (Proj.toSpecZero (grading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  refine ⟨z, hz, g, AllCharacteristics.spec_preimage_surjective_of_closedImmersion qU, ?_, ?_⟩
  · have he : CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) ≫
        CommRingCat.ofHom g = CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← hj, ← Category.assoc, hU,
        finiteSchemeCoefficient_spec (i ≫ toBase I)]
      exact Category.assoc _ _ _
    exact congrArg CommRingCat.Hom.hom he
  · exact (congrArg (· ≫ j) hg).trans hU

end
end PfaffianDescent
