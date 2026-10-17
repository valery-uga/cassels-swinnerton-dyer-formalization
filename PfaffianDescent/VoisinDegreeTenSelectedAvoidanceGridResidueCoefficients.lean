import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericCoefficients
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_canonicalSixteen_coefficients_at_residueFactor
    {K E : Type u} [Field K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 16).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (z : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (hz : configurationQuotientMap (equationIdeal p hp) 16 z =
      (cubicConfigurationBase p hp 16).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 16))
        (IsLocalRing.closedPoint (cubicConfigurationBase p hp 16).functionField))
    (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
    (g : (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.residueField z →+* E)
    (hg : Spec.map (CommRingCat.ofHom g) ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left.fromSpecResidueField z = c) :
    (g.comp (cubicSixteenOrderedLiftFunctionFieldHom p hp z hz)).comp a.hom =
      (Spec.preimage (c ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom)).hom := by
  let O := (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
  let b := cubicSixteenOrderedLiftFunctionFieldHom p hp z hz
  have hb := voisinDegreeTenSelectedAvoidance_sixteenFunctionFieldHom_comp_cubicCoefficients
    p hp a ha z hz
  have hspecb : Spec.map (CommRingCat.ofHom (b.comp a.hom)) =
      O.fromSpecResidueField z ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 16).hom := by
    rw [hb]
    exact Spec.map_preimage _
  have hspec := congrArg (fun f => Spec.map (CommRingCat.ofHom g) ≫ f) hspecb
  rw [← Spec.map_comp, ← Category.assoc, hg] at hspec
  have hpre := congrArg Spec.preimage hspec
  rw [Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

end PfaffianDescent
