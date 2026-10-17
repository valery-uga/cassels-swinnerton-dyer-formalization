import PfaffianDescent.VoisinGenericResidueChartLift
import PfaffianDescent.VoisinCanonicalOrderedGenericPoint
import AllCharacteristics.OrderedConfigurationProjectiveIncidence

/-! The selected chart coordinate is the canonical ordered generic marked point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

/-- At the generic residue field of the canonical ordered configuration,
each selected affine chart lift gives its actual marked point on the cubic. -/
theorem cubicOrderedPointOverGeneric_chartCoordinate
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    {U W : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
    (j : W ⟶ (Over.mk (hypersurfaceToBase p hp)).left)
    (t : Fin 8 → (U ⟶ W))
    (ht : ∀ k, t k ≫ j =
      (i ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)
    (k : Fin 8) :
    HEq ((openImmersion_genericResidueLift i ≫ t k) ≫ j)
      ((orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left.fromSpecResidueField z ≫
        (Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)) := by
  rw [cubicOrderedPointOverGeneric_eq_chartGenericImage p hp i z hz]
  apply heq_of_eq
  exact openImmersion_genericResidueLift_coordinate_comp i (t k) j _
    (by
      rw [← Category.assoc]
      exact ht k)

end PfaffianDescent
