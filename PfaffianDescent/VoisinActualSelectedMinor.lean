import PfaffianDescent.VoisinActualCanonicalMinor
import PfaffianDescent.VoisinActualEightComparison
import PfaffianDescent.VoisinEightPointComparisonMinor

/-! The selected normalized eight vectors inherit the canonical
geometric presentation's unit quadratic minor. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ActualGenericEightPresentation.exists_selected_unitQuadraticMinor
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
    ∃ m : Fin 8 ↪ Monomials (Fin 4) 2,
      IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (w.selectedVectors p hp a ha i hz)).det := by
  dsimp only
  let Q := cubicConfigurationBase p hp 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let bCan := quadraticOrderedLiftFunctionFieldHom p hp
    (i (genericPoint U)) hz
  let bSel : K →+* O.residueField (i (genericPoint U)) :=
    (Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)).hom
  letI : Algebra Q.functionField (O.residueField (i (genericPoint U))) :=
    bCan.toAlgebra
  letI : Algebra K (O.residueField (i (genericPoint U))) := bSel.toAlgebra
  obtain ⟨m, hm⟩ := w.exists_canonical_unitQuadraticMinor p hp a ha i hz
  obtain ⟨c, hx, hy⟩ := w.exists_comparison p hp a ha i hz
  have hmy : IsUnit (eightPointQuadraticEvaluationMinor m c.y).det := by
    rw [hy]
    exact hm
  have hmx := (c.minor_isUnit_iff a.hom p hp
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q.functionField)) m).mp hmy
  rw [hx] at hmx
  exact ⟨m, hmx⟩

end PfaffianDescent
