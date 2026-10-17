import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericRegularTriple
import PfaffianDescent.VoisinDegreeTenComplementCycle
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericSixteen_exists_effectiveCycle_degree_eleven
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (hypersurface (p.map a.hom) (hp.map a.hom)),
      EffectiveZeroCycle.degree (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 11 := by
  let Q := cubicConfigurationBase p hp 16
  letI : Field Q.functionField := inferInstance
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  letI : CommRing Γ(D.val.subscheme, ⊤) := inferInstance
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : CharZero Q.functionField := charZero_cubicConfigurationFunctionField_of_flat p hp 16
  letI : Infinite Q.functionField := CharZero.infinite Q.functionField
  obtain ⟨T, q, r, hxsurj, hpx, hq, hqx, hq0, hrel, hr, hrx, hregular⟩ :=
    voisinDegreeTenSelectedAvoidance_genericSixteen_exists_nativeChart_regularTriple
      (L := L) p hp a ha hno
  have hellOne : T.ell.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x = 1 := by
    simpa only [Ideal.Quotient.lift_mk, MvPolynomial.coe_eval₂Hom] using T.hellOne
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  have hp'0 := cubicConfigurationCoefficientChange_ne_zero p hp 16 a hp0
  exact finiteSubschemeDatum_degree_sixteen_complement_cycle_degree_eleven_of_selected_coordinates
    (p.map a.hom) q r (hp.map a.hom) hq hr hp'0 hq0 hrel hregular D
    ⟨T.x, T.ell, hxsurj, T.hell, hellOne, hpx, hqx, hrx⟩
end PfaffianDescent
