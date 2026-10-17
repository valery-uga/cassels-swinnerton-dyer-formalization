import PfaffianDescent.VoisinCanonicalCubicCoefficientMap
import PfaffianDescent.VoisinCanonicalOrderedGenericPoint
import PfaffianDescent.VoisinGenericResidueChartLift

/-! Cubic coefficient compatibility between selected and canonical generic points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The selected chart generic residue point and the canonical ordered
generic configuration induce the same map from the original cubic
coefficient field, after transporting their equal residue-field types. -/
theorem cubicOrderedPointOverGeneric_selectedCubicCoefficients
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (α : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (hα : Spec.map α = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 8 z =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField)) :
    HEq ((quadraticOrderedLiftFunctionFieldHom p hp z hz).comp α.hom)
      ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)).hom) := by
  have hzi := cubicOrderedPointOverGeneric_eq_chartGenericImage p hp i z hz
  subst z
  apply heq_of_eq
  rw [quadraticOrderedLiftFunctionFieldHom_comp_cubicCoefficients
    p hp α hα (i (genericPoint U)) hz]
  congr 1
  rw [← Category.assoc, openImmersion_genericResidueLift_comp]

end PfaffianDescent
