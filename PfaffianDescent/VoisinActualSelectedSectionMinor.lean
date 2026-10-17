import PfaffianDescent.VoisinActualSelectedMinor
import PfaffianDescent.VoisinActualSelectedVectorSections

/-! The actual selected chart's regular coordinate sections have a
unit quadratic evaluation minor at their generic residue-field point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.exists_pulledSections_unitQuadraticMinor
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
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (fun k j => f (x k j))).det := by
  dsimp only
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let F := O.residueField (i (genericPoint U))
  let s := openImmersion_genericResidueLift i
  let f : Γ(U, ⊤) →+* F :=
    (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) w.zc w.hzc U w.t
  obtain ⟨m, hm⟩ := w.exists_selected_unitQuadraticMinor p hp a ha i hz
  have hs : w.selectedVectors p hp a ha i hz =
      (fun k j => f (x k j)) := by
    funext k j
    exact w.selectedVectors_eq_pulledSections p hp a ha i hz k j
  rw [hs] at hm
  exact ⟨m, hm⟩

end PfaffianDescent
