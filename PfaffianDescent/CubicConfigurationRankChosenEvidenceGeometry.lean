import PfaffianDescent.CubicConfigurationOrderedChosenSectionsNativeGeometry
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedSectionEvidence

/-! Assemble ordered geometry from one exact evidence record, before
specializing its parameter and zero-family schemes to a pulled Serre module.
The original point and its avoidance are the same rank-coordinate point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def cubicConfigurationRankChosenEvidence_geometry
    {K E : Type u} [Field K] [CharZero K] [Field E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    {Rk : Scheme.{u}}
    (cA : Spec (.of E) ⟶ Rk)
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (β : (cubicConfigurationBase p hp 3).functionField →+* E)
    (hβ : Spec.map (CommRingCat.ofHom β) ≫
      (cubicConfigurationBase p hp 3).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 3)) =
      (cA ≫ aRank) ≫ configurationQuotientMap (equationIdeal p hp) 3)
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι] :=
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let f := cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp
  fun {P Q Z : Scheme.{u}}
    (pp : P ⟶ Spec (.of F)) (qp : Q ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
    (q : Spec (.of F) ⟶ Q) (hq : q ≫ qp = 𝟙 _)
    (v : Q ⟶ P) (hv : v ≫ pp = qp)
    (n : Fin 3)
    (evidence : SerreActualChosenMarkedSectionEvidence x pp zero
      ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v) n f
      (cA ≫ (aRank ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)))
    (havoid : (cA ≫ aRank ≫
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
        (IsLocalRing.closedPoint E) ∉ Set.range ι) =>
    have hOriginal : serreActualChosenFibre_marked x pp zero
        ((Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ q) ≫ v)
        evidence.sections.δ n ≫
        cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp =
      ((cA ≫ aRank) ≫ (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left :=
      evidence.facts.originalSurface.trans (by simp only [Category.assoc])
    have hOriginalAvoid : (((cA ≫ aRank) ≫
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
        (IsLocalRing.closedPoint E) ∉ Set.range ι := by
      simpa only [Category.assoc] using havoid
    cubicConfigurationOrderedThreeChosenSections_nativeGeometry
      p hp hp0 (cA ≫ aRank) β hβ a ha ι pp qp zero q hq v hv
      evidence.sections n evidence.facts.stalk hOriginal hOriginalAvoid

end PfaffianDescent
