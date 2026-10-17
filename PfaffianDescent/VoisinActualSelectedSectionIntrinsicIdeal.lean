import PfaffianDescent.VoisinActualSelectedVectorSections
import PfaffianDescent.VoisinActualEightIntrinsicIdealEquality

/-! The canonical finite-algebra intrinsic ideal equals the intrinsic
ideal formed from the selected chart's regular coordinate sections. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.intrinsicIdeal_eq_pulledSections
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
    letI : Algebra Q.functionField F := bCan.toAlgebra
    letI : Algebra K F := bSel.toAlgebra
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map bSel) (hp.map bSel)
      (w.canonicalVectors p hp a ha i hz) =
    intrinsicEightPointTripleHomogeneousIdeal
      (p.map bSel) (hp.map bSel)
      (fun k j => f (x k j)) := by
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
  letI : Algebra Q.functionField F := bCan.toAlgebra
  letI : Algebra K F := bSel.toAlgebra
  have hs : w.selectedVectors p hp a ha i hz =
      (fun k j => f (x k j)) := by
    funext k j
    exact w.selectedVectors_eq_pulledSections p hp a ha i hz k j
  rw [← hs]
  exact w.intrinsicIdeal_eq p hp a ha i hz

end PfaffianDescent
