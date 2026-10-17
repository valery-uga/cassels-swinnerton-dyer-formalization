import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericNoSection
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridLineSectionEtale
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericCoefficientChange_exists_etaleThreeDatum
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
      ∃ D₃ : FiniteSubschemeDatum (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 3,
        Etale (D₃.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D
  intro a ha
  let F := (cubicConfigurationBase p hp n).functionField
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp n
  letI : Infinite F := CharZero.infinite F
  have hnoF := voisinDegreeTenSelectedAvoidance_genericCoefficientChange_no_section
    n p hp hp0 D hno a ha
  have hP0 := cubicConfigurationCoefficientChange_ne_zero p hp n a hp0
  let D₃ := cubicLineSectionDatum (by decide : 2 ≤ 4) (p.map a.hom) (hp.map a.hom) hP0
  exact ⟨D₃, voisinDegreeTenSelectedAvoidance_lineSectionDatum_etale_of_no_section
    (p.map a.hom) (hp.map a.hom) hP0 hnoF⟩
end PfaffianDescent
