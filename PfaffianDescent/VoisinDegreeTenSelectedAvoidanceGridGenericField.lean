import PfaffianDescent.VoisinFiniteGenericFiberPoint
import PfaffianDescent.VoisinGenericCubicSixteenEvaluation
import PfaffianDescent.VoisinSelectedLocalizationFractionField
import AllCharacteristics.VoisinGenericCubicConfiguration

/-! Canonical ordered generic sixteen-point field comparison. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ordered configuration point chosen over the generic unordered cubic
configuration is forced to be the generic point of the ordered scheme. -/
theorem voisinDegreeTenSelectedAvoidance_orderedGenericSixteen_eq_generic
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 16).functionField)) :
    z = genericPoint
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left := by
  letI : IsIntegral (orderedFamilyConfigurationOver
      (toBase (equationIdeal p hp)) 16).left := by
    change IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left
    infer_instance
  letI : IsIntegral (configurationQuotientOpen (equationIdeal p hp) 16).toScheme := by
    change IsIntegral (cubicConfigurationBase p hp 16)
    infer_instance
  have hgeneric : configurationQuotientMap (equationIdeal p hp) 16 z =
      genericPoint (cubicConfigurationBase p hp 16) :=
    hz.trans Scheme.fromSpecStalk_closedPoint
  exact finiteSurjective_pointOverGeneric_eq_generic
    (configurationQuotientMap (equationIdeal p hp) 16) z hgeneric

/-- The generic image of any integral ordered affine open is the same
ordered point that lies over the generic unordered quotient. -/
theorem voisinDegreeTenSelectedAvoidance_orderedGenericSixteen_eq_chartGenericImage
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left) [IsOpenImmersion i]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 16).functionField)) :
    z = i (genericPoint U) := by
  rw [genericPoint_eq_of_isOpenImmersion i]
  exact voisinDegreeTenSelectedAvoidance_orderedGenericSixteen_eq_generic p hp z hz

/-- The selected determinant-open chart field is literally equivalent to
the residue field at the canonical ordered point over the generic quotient. -/
noncomputable def voisinDegreeTenSelectedAvoidance_orderedGenericSixteen_localizedFractionEquivResidueField
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    {U : Scheme.{u}} [IsAffine U] [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left) [IsOpenImmersion i]
    (s : Γ(U, ⊤)) (hs : s ≠ 0)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 16).functionField)) :
    FractionRing (Localization.Away s) ≃+*
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 16).left.residueField z := by
  rw [voisinDegreeTenSelectedAvoidance_orderedGenericSixteen_eq_chartGenericImage p hp i z hz]
  exact affineOpenImmersion_localizedFractionEquivGenericImageResidueField i s hs

end PfaffianDescent
