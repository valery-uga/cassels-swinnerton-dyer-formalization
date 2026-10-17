import PfaffianDescent.VoisinActualEightPresentation
import PfaffianDescent.VoisinPulledEightGenericEvaluation

/-! The actual selected normalized vectors are the generic residue-field
values of the regular coordinate sections on the selected affine chart. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.selectedVectors_eq_pulledSections
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
    let F := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left.residueField (i (genericPoint U))
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    let x := pulledEightLinearChartCoordinates
      (equationIdeal p hp) w.zc w.hzc U w.t
    ∀ k j, w.selectedVectors p hp a ha i hz k j = f (x k j) := by
  dsimp only
  intro k j
  exact pulledEightAffineSections_genericFieldValue U
    (openImmersion_genericResidueLift i) w.t
    (fun j => linearChartCoordinate (equationIdeal p hp) w.zc w.hzc j) k j

end PfaffianDescent
