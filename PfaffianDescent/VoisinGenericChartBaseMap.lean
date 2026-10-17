import PfaffianDescent.VoisinPulledChartEquationVanishing

/-! Base-field compatibility for the selected affine chart at a field point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluating any ordered coordinate chart at a field-valued point gives
the same coefficient-field homomorphism as evaluating the configuration's
base map at that point. -/
theorem orderedChartLift_fieldPoint_baseRingHom
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (i : U ⟶ (AllCharacteristics.orderedFamilyConfigurationOver
      (toBase I) 8).left)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I) z))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) z hz
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι (toBase I) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate (toBase I) 8 k).left)
    (a : Spec (.of F) ⟶ U) (k : Fin 8) :
    (Spec.preimage (a ≫ t k)).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
    (Spec.preimage (a ≫ i ≫
      (AllCharacteristics.orderedFamilyConfigurationOver
        (toBase I) 8).hom)).hom := by
  have hscheme := congrArg
    (fun v : U ⟶ Spec (.of K) => a ≫ v)
    (orderedChartLift_baseMap I z hz U i t ht k)
  have hpre := congrArg Spec.preimage hscheme
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

end PfaffianDescent
