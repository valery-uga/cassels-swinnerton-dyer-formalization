import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionGeometryDataProvider
import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedCanonicalFinite

/-! Actual native finite chosen-fibre provider.
Only the SAME old seed's actual hgood is required. No new seed, new goodOpen,
chosen finiteness, or geometry/Evidence certificate is supplied. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- SAME original incidence family's actual finite-good open. -/
def serreActualNativeMarkedInputsOriginalSectionIncidenceGoodOpen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IA : Type u} [Fintype IA] [DecidableEq IA]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  cubicClosedPointSerreFiniteZeroResidual_goodOpen
    (serreThreePointSectionIncidenceZeroFamily
      (serreActualNativeRankConfiguration p hp aRank) (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (serreActualNativeRankMarked p hp aRank)
      (serreActualNativeRankMarked_toBase p hp aRank)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))

@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsFiniteChosenProvider
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 3)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
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
    (β : (cubicConfigurationBase p hp 3).functionField →+*
      Rk.residueField (genericPoint Rk))
    (G : Matrix (Fin 9) (Fin 3) (cubicConfigurationBase p hp 3).functionField)
    (H : Matrix (Fin 3) (Fin 9) (cubicConfigurationBase p hp 3).functionField)
    (hHG : H * G = 1)
    (qF : Spec (.of (cubicConfigurationBase p hp 3).functionField) ⟶
      scheme (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 3) (cubicConfigurationBase p hp 3).functionField)))
    (s : Spec (.of (Rk.residueField (genericPoint Rk))) ⟶
      serreActualNativeOriginalSectionIncidence p hp e A aRank)
    (hsp : letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
      s ≫ serreActualNativeOriginalSectionIncidenceToParameters p hp e A aRank =
        serreActualNativeSelectedResidueParameter β qF ≫
          serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
    (hgood : s (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∈
      serreActualNativeMarkedInputsOriginalSectionIncidenceGoodOpen p hp e A aRank) :=
  letI : Algebra K (cubicConfigurationBase p hp 3).functionField := a.hom.toAlgebra
  serreActualCubicGroundFamily_oldGoodSeed_canonicalNewFibre_finite
    p hp e C h9 A B G H hHG (serreActualNativeSelectedResidueParameter β qF)
    (serreActualNativeRankConfiguration p hp aRank)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank) s hsp hgood

end PfaffianDescent
