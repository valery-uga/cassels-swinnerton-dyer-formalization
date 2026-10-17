import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization
import PfaffianDescent.SectionCycles
import PfaffianDescent.ResidualCycles
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericCoefficientChange_no_section
    {K : Type u} [Field K] [CharZero K] (n : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    letI : IsIntegral (cubicConfigurationBase p hp n) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n),
      ¬ ∃ s : Spec (.of (cubicConfigurationBase p hp n).functionField) ⟶
          hypersurface (p.map a.hom) (hp.map a.hom),
        s ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom) = 𝟙 _ := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  intro a ha hsection
  obtain ⟨s, hs⟩ := hsection
  obtain ⟨zη, hzη⟩ := effective_cycle_of_section
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) s hs 1
  obtain ⟨z, hz⟩ := effectiveCycle_of_genericEffectiveCycle n p hp hp0 D a ha zη
  apply hno
  exact section_of_effective_cycle_degree_one (hypersurfaceToBase p hp) z (hz.trans hzη)
end PfaffianDescent
