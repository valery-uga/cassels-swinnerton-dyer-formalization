import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericSelectedChart
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridChartRegularTriple

/-! Literal regular cubic triple through the actual unordered generic sixteen datum. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericSixteen_exists_nativeChart_regularTriple
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    let Q := cubicConfigurationBase p hp 16
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
    ∃ (T : NormalizedAmbientChart Q.functionField Γ(D.val.subscheme, ⊤) (Fin 4)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField)) j)
      (q r : MvPolynomial (Fin 4) Q.functionField),
      Function.Surjective (eval₂Hom
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x) ∧
      (p.map a.hom).eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x = 0 ∧
      q ≠ 0 ∧ IsRelPrime (p.map a.hom) q ∧
      r.IsHomogeneous 3 ∧ r.eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x = 0 ∧
      ∀ y : MvPolynomial (Fin 4) Q.functionField,
        r * y ∈ Ideal.span ({p.map a.hom, q} : Set _) →
          y ∈ Ideal.span ({p.map a.hom, q} : Set _) := by
  dsimp only
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
  letI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  letI : CharZero Q.functionField := charZero_cubicConfigurationFunctionField_of_flat p hp 16
  letI : Infinite Q.functionField := CharZero.infinite Q.functionField
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 16 a
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  have hp'0 := cubicConfigurationCoefficientChange_ne_zero p hp 16 a hp0
  have hA : finrank Q.functionField Γ(D.val.subscheme, ⊤) = 16 :=
    cubicConfigurationGenericSixteen_coefficientFinrank p hp a ha
  exact voisinDegreeTenSelectedAvoidance_exists_chartRegularTriple_of_nativeAvoidance
    (F := Q.functionField) (A := Γ(D.val.subscheme, ⊤))
    (p.map a.hom) (hp.map a.hom) hp'0
    (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)) hA
    (voisinDegreeTenSelectedAvoidance_genericSixteen_exists_nativeChart_associatedPrimeAvoidance
      (L := L) p hp a ha hno)

end PfaffianDescent
