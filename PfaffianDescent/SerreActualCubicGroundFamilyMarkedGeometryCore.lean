import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionGeometryDataProvider
import PfaffianDescent.SerreActualCubicGroundFamilyMarkedGeometryCoreType
import PfaffianDescent.SerreActualCubicGroundFamilyOldSelectedNativeGoodMembership
import PfaffianDescent.SerreActualChosenMarkedResidualGeometry
import PfaffianDescent.SerreActualChosenMarkedResidualGeometryOfSection
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGroundSelectedCanonicalMarked
import PfaffianDescent.SerreActualGroundFamilyLiteralMarkedSurfaceOriginal
import PfaffianDescent.CubicConfigurationOrderedFieldCoefficientMarkedIdentification
import PfaffianDescent.SerreActualChosenMarkedParameterAssociationPointSurface
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedStalk
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedSurface
import PfaffianDescent.SerreActualCubicGroundFamilyLiteralTransportedMarkedSectionEvidence
import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedNewMarkedGoodOpen
import PfaffianDescent.SerreActualCubicGroundFamilyOldSeedNewMarkedSupportAvoidance
import PfaffianDescent.CubicConfigurationGenericMarkedOutsideSupport
import PfaffianDescent.CubicConfigurationRankChosenEvidenceGeometry
import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionEvidenceProvider


/-! The original selected incidence data produce the exact native marked
geometry contract through the checked staged DATA constructor. The section
Evidence and geometry are constructed internally; no certificate is assumed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

set_option profiler true in
set_option profiler.threshold 1000 in
set_option maxHeartbeats 250000 in
theorem serreActualCubicGroundFamily_selectedSeed_markedGeometryCore_nonempty
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι]
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {IA IB : Type u} [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (havoid : (Rk.fromSpecResidueField (genericPoint Rk) ≫ aRank ≫
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 (0 : Fin 3)).left)
        (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∉ Set.range ι) :
  Nonempty (serreActualCubicGroundFamily_selectedSeed_markedGeometryCoreType p hp hp0 a ha ι e C h9 A B aRank havoid) := by
  refine ⟨?_⟩
  unfold serreActualCubicGroundFamily_selectedSeed_markedGeometryCoreType
  -- Introduce the existing let bindings without rebuilding or zeta-expanding
  -- the pulled module, its zero family, or the native support-field instance.
  -- `letI` is inlined by elaboration, so only ordinary lets consume names.
  intro F E cA c cfg marked hm x M pp zero D₃ j₃ f
    β hβ G H hHG qF hqF r bE s hsp hcfg hmarked
  exact serreActualCubicGroundFamily_nativeOriginalSelectedSectionGeometryDataProvider
    p hp hp0 a ha ι e C h9 A B aRank β hβ G H hHG qF hqF
    s hsp hmarked hcfg (0 : Fin 3) havoid



@[irreducible]
def serreActualCubicGroundFamily_selectedSeed_markedGeometryCore
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [Nonempty (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫ cubicConfigurationToBase p hp 3)
    {D : Scheme.{u}} [IsAffine D]
    (ι : D ⟶ hypersurface p hp) [IsClosedImmersion ι]
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {IA IB : Type u} [Fintype IA] [DecidableEq IA] [Fintype IB] [DecidableEq IB]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    (B : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      SchemeModuleFiniteFreeAffineCover
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K (cubicConfigurationBase p hp 3).functionField) p hp)).obj e.E) IB)
    {Rk : Scheme.{u}} [IsIntegral Rk]
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion aRank]
    (havoid : (Rk.fromSpecResidueField (genericPoint Rk) ≫ aRank ≫
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 (0 : Fin 3)).left)
        (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∉ Set.range ι) :
  serreActualCubicGroundFamily_selectedSeed_markedGeometryCoreType p hp hp0 a ha ι e C h9 A B aRank havoid :=
  Classical.choice (serreActualCubicGroundFamily_selectedSeed_markedGeometryCore_nonempty p hp hp0 a ha ι e C h9 A B aRank havoid)


end PfaffianDescent
