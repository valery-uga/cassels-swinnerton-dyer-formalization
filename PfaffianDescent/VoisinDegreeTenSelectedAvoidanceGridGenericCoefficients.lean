import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericField

/-! Agreement of cubic coefficients at the canonical ordered generic point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coefficient field reaches the ordered generic residue field either
through the unordered configuration function field or through the actual
ordered configuration base map, with identical results. -/
theorem voisinDegreeTenSelectedAvoidance_sixteenFunctionFieldHom_comp_cubicCoefficients
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 16).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 16).functionField)) :
    (cubicSixteenOrderedLiftFunctionFieldHom p hp z hz).comp a.hom =
      (Spec.preimage
        ((orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 16).left.fromSpecResidueField z ≫
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase p hp) 16).hom)).hom := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 16).left
  let Q := cubicConfigurationBase p hp 16
  let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
  let π : O ⟶ Q := configurationQuotientMap (equationIdeal p hp) 16
  have hspec : Spec.map (CommRingCat.ofHom b) ≫
      Q.fromSpecStalk (genericPoint Q) = O.fromSpecResidueField z ≫ π :=
    cubicSixteenOrderedLiftFunctionFieldHom_spec p hp z hz
  have hbase : π ≫ cubicConfigurationToBase p hp 16 =
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 16).hom :=
    configurationQuotientMap_toBase (equationIdeal p hp) 16
  have hschemes : Spec.map (CommRingCat.ofHom (b.comp a.hom)) =
      O.fromSpecResidueField z ≫
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom := by
    change Spec.map (a ≫ CommRingCat.ofHom b) = _
    rw [Spec.map_comp, ha]
    calc
      Spec.map (CommRingCat.ofHom b) ≫
          (Q.fromSpecStalk (genericPoint Q) ≫ cubicConfigurationToBase p hp 16) =
        (Spec.map (CommRingCat.ofHom b) ≫
          Q.fromSpecStalk (genericPoint Q)) ≫
            cubicConfigurationToBase p hp 16 := (Category.assoc _ _ _).symm
      _ = (O.fromSpecResidueField z ≫ π) ≫
          cubicConfigurationToBase p hp 16 := by rw [hspec]
      _ = O.fromSpecResidueField z ≫
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom := by
        rw [Category.assoc, hbase]
  have hpre := congrArg Spec.preimage hschemes
  rw [Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

end PfaffianDescent
