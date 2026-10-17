import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridIntegralBase
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_sixteenConfiguration_integral_of_no_section
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left ∧
      IsIntegral (cubicConfigurationBase p hp 16) := by
  obtain ⟨v, hv0, hpv, A, _, hAbase, hAcoord, _, hcubic, hqzero, hrzero⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_original_configuration
      (L := AlgebraicClosure K) p hp hno
  exact voisinDegreeTenSelectedAvoidance_configuration_integral_of_fieldPoint p hp
    (voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno) 16 A
end PfaffianDescent
