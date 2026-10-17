import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericAssociatedAvoidance
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridNativeChart

/-! A chosen common chart of the actual unordered generic sixteen-point datum,
with its literal immersion, coefficient evaluation, and cubic avoidance. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericSixteen_exists_nativeChart_associatedPrimeAvoidance
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
  letI : CommRing Γ(D.val.subscheme, ⊤) := inferInstance
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    let j := D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)
    ∃ T : NormalizedAmbientChart Q.functionField Γ(D.val.subscheme, ⊤) (Fin 4)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField)) j,
      Function.Surjective (eval₂Hom
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x) ∧
      (p.map a.hom).eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.x = 0 ∧
      ∀ (q : MvPolynomial (Fin 4) Q.functionField), q.IsHomogeneous 3 →
        IsRelPrime (p.map a.hom) q →
        ∀ P ∈ associatedPrimes
            (MvPolynomial (Fin 4) Q.functionField ⧸ Ideal.span ({p.map a.hom, q} : Set _))
            (MvPolynomial (Fin 4) Q.functionField ⧸ Ideal.span ({p.map a.hom, q} : Set _)),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
              (K := Q.functionField) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) T.x 3,
            Ideal.Quotient.mk (Ideal.span ({p.map a.hom, q} : Set _)) r ∉ P := by
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  letI : Field Q.functionField := inferInstance
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : CharZero Q.functionField := charZero_cubicConfigurationFunctionField_of_flat p hp 16
  letI : Infinite Q.functionField := CharZero.infinite Q.functionField
  have hchart := voisinDegreeTenSelectedAvoidance_exists_nativeFiniteChart
    (p.map a.hom) (hp.map a.hom) D.val.subschemeι
  let T : NormalizedAmbientChart Q.functionField Γ(D.val.subscheme, ⊤) (Fin 4)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q.functionField))
      (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom)) := Classical.choose hchart
  have hT := Classical.choose_spec hchart
  refine ⟨T, hT.1, hT.2, ?_⟩
  exact voisinDegreeTenSelectedAvoidance_genericSixteen_nativeCubicKernel_associatedPrimeAvoidance
    (L := L) p hp a ha hno T

end PfaffianDescent
