import PfaffianDescent.VoisinGenericChartBaseMap
import PfaffianDescent.VoisinChartSchemePointNormalized

/-! The eight ordered coordinate-chart lifts give normalized projective vectors. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At any field-valued point of an ordered configuration, every coordinate
lift into one affine Proj chart reconstructs a normalized homogeneous vector
for that marked projective point. The coefficient-field structure is the
one induced by the configuration base map. -/
theorem orderedChartLift_fieldPoint_normalizedPointAt
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellz : Ideal.Quotient.mk I.toIdeal ell = z)
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
    let b : K →+* F := (Spec.preimage (a ≫ i ≫
      (AllCharacteristics.orderedFamilyConfigurationOver
        (toBase I) 8).hom)).hom
    letI : Algebra K F := b.toAlgebra
    let x : Fin 4 → F := fun j =>
      (Spec.preimage (a ≫ t k)).hom (linearChartCoordinate I z hz j)
    ell.eval₂ (algebraMap K F) x = 1 ∧
    ∃ (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) z = 1),
      linearNormalizedPointAt I x he z hz hzOne =
        (a ≫ t k) ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
  dsimp only
  let b : K →+* F := (Spec.preimage (a ≫ i ≫
    (AllCharacteristics.orderedFamilyConfigurationOver (toBase I) 8).hom)).hom
  letI : Algebra K F := b.toAlgebra
  have hbase : (Spec.preimage (a ≫ t k)).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
        algebraMap K F := by
    change (Spec.preimage (a ≫ t k)).hom.comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) = b
    exact orderedChartLift_fieldPoint_baseRingHom I z hz U i t ht a k
  exact chartSchemePoint_normalizedPointAt I z hz ell hell hellz
    (a ≫ t k) hbase

end PfaffianDescent
