import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericComplementCycle
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceCompletionEtale
import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_effectiveDegreeEleven_of_etaleSixteen
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 16)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  letI : IsIntegral (cubicConfigurationBase p hp 16) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 16 D
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 16
  obtain ⟨zη, hzη⟩ :=
    voisinDegreeTenSelectedAvoidance_genericSixteen_exists_effectiveCycle_degree_eleven
      (L := AlgebraicClosure K) p hp a ha hno
  obtain ⟨z, hz⟩ := effectiveCycle_of_genericEffectiveCycle 16 p hp hp0 D a ha zη
  exact ⟨z, hz.trans hzη⟩

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_effectiveDegreeEleven_of_etaleTen
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  letI : Infinite K := CharZero.infinite K
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  let C : DegreeTenRankSixteenCompletion p hp D₁₀ := Classical.choice
    (nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field p hp hp0 D₁₀)
  letI : Etale (C.datum.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    voisinDegreeTenSelectedAvoidance_completion_datum_etale p hp hno D₁₀ C
  exact voisinDegreeTenSelectedAvoidance_exists_effectiveDegreeEleven_of_etaleSixteen
    p hp C.datum hno
end PfaffianDescent
