import PfaffianDescent.VoisinActualSelectedSectionIntrinsicIdeal
import PfaffianDescent.VoisinActualSelectedSectionMinor
import PfaffianDescent.VoisinActualSelectedCoefficientMap
import PfaffianDescent.VoisinSelectedFrameCoefficientSpecialization

/-! The actual generic selected quadratic frame cuts out the canonical
finite-algebra intrinsic ideal over the ordered generic residue field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.intrinsicIdeal_eq_selectedFrameFiber
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (w : ActualGenericEightPresentation p hp a ha i hz) :
    let Q := cubicConfigurationBase p hp 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let F := O.residueField (i (genericPoint U))
    let bCan := quadraticOrderedLiftFunctionFieldHom p hp
      (i (genericPoint U)) hz
    let bSel : K →+* F :=
      (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    let x := pulledEightLinearChartCoordinates
      (equationIdeal p hp) w.zc w.hzc U w.t
    let β := affineFunctionHom (i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)
    letI : Algebra Q.functionField F := bCan.toAlgebra
    letI : Algebra K F := bSel.toAlgebra
    ∀ (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (hm : IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (fun k j => f (x k j))).det),
      let S := Localization.Away (quadraticMinorDet m x)
      let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
      let pS := p.map βS
      let hpS := hp.map βS
      let g := quadraticMinorSelectedPointLift m x f hm
      intrinsicEightPointTripleHomogeneousIdeal
        (p.map bSel) (hp.map bSel)
        (w.canonicalVectors p hp a ha i hz) =
      relativeTripleIntersectionHomogeneousIdeal
        (pS.map g)
        ((quadraticSelectedOpenPolynomial m x 0).map g)
        ((quadraticSelectedOpenPolynomial m x 1).map g)
        (hpS.map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m x 0).map g)
        ((quadraticSelectedOpenPolynomial_isHomogeneous m x 1).map g) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let F := O.residueField (i (genericPoint U))
  let bCan := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  let bSel : K →+* F :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)).hom
  let s := openImmersion_genericResidueLift i
  let f : Γ(U, ⊤) →+* F :=
    (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) w.zc w.hzc U w.t
  let β := affineFunctionHom (i ≫
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom)
  letI : Algebra Q.functionField F := bCan.toAlgebra
  letI : Algebra K F := bSel.toAlgebra
  intro m hm
  have hid := w.intrinsicIdeal_eq_pulledSections p hp a ha i hz
  have hframe :=
    selectedIntrinsicEightPointTriple_eq_specializedFrame_with_coefficients
      m x p hp β f hm
  have hcoeff : f.comp β = bSel := selectedGeneric_coefficientMap_eq p hp i
  dsimp only at hid hframe
  rw [hcoeff] at hframe
  exact hid.trans hframe

end PfaffianDescent
