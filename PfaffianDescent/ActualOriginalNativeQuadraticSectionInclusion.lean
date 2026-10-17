import PfaffianDescent.ActualIdealTwistRestrictionSectionSquare
import PfaffianDescent.ActualOriginalAmbientIdealQuadraticNativeTwistRestriction
import PfaffianDescent.ActualP3IdealQuadraticDictionaryInclusion
import PfaffianDescent.ActualP3HomogeneousSectionUnitHom
import PfaffianDescent.ActualPositiveGradedHomogeneousSectionPullback

/- SOURCE ONLY / UNVERIFIED. The genuine ambient H0 section restricted
to the SAME cubic ideal and native O2 has EXACTLY its actual quotient
homogeneous section under the actual native ideal inclusion.
No map equality or section comparison certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison

lemma actualOriginalAmbientIdealQuadraticNativeTwistRestriction_inclusion
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let i := quotientProjMap I
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let Q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2 :=
      ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).val,
        (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).property.1⟩
    actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s ≫
        actualIdealTwistInclusion q (positiveSheafOfModules (grading I) 2) =
      (positiveSheafOfModules (grading I) 2).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 2
          ⟨Ideal.Quotient.mk I.toIdeal Q, (quotientGradedRingHom I).2 Q.property⟩) := by
  dsimp only
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let i := quotientProjMap I
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion i := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (q ≫ i) := IsClosedImmersion.comp q i
  let T := positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2
  let N := positiveSheafOfModules (grading I) 2
  let Q : MvPolynomial.homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).val,
      (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).property.1⟩
  have hincl : s ≫ actualIdealTwistInclusion (q ≫ i) T =
      T.unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2 Q) := by
    exact (p3ActualIdealQuadraticIntrinsicLinearEquiv_inclusion (q ≫ i) s).trans
      (p3HomogeneousGlobalSectionLinearMap_unitHom K 2 Q)
  have h := actualIdealTwistGlobalRestriction_nativeInclusion
    (ambientToBase (R := K) (σ := Fin 4)) i q T N
    (actualAmbientPositiveTwistQuotientIso I 2) s
  have hmap := congrArg (fun a : schemeModuleUnit
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) ⟶ T =>
    inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map a ≫
      (actualAmbientPositiveTwistQuotientIso I 2).hom) hincl
  have hsection := actualAmbientPositiveTwistQuotientIso_homogeneousSection I 2 Q
  change ((actualClosedImmersionFactorIdealTwistGlobalSectionsRestriction
      (ambientToBase (R := K) (σ := Fin 4)) i q T s) ≫
      schemeModuleTensorMap (𝟙 (closedImmersionModule q))
        (actualAmbientPositiveTwistQuotientIso I 2).hom) ≫
        actualIdealTwistInclusion q N = _
  exact (Category.assoc
    (actualClosedImmersionFactorIdealTwistGlobalSectionsRestriction
      (ambientToBase (R := K) (σ := Fin 4)) i q T s)
    (schemeModuleTensorMap (𝟙 (closedImmersionModule q))
      (actualAmbientPositiveTwistQuotientIso I 2).hom)
    (actualIdealTwistInclusion q N)).trans (h.trans (hmap.trans hsection))

end PfaffianDescent
