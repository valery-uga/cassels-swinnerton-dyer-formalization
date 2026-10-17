import PfaffianDescent.SerreActualCubicGroundFamilyNativeResidueParameterMarkedEvidenceProvider

/-! Literal native selected-section data at the actual residue-field point.
Small incidence helpers derive the zero closed immersion internally. The data
provider retains original section hypotheses and assumes no Evidence record. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual generic-point residue-field morphism of the original rank chart. -/
def serreActualNativeOriginalResidueConfigurationPoint
    (Rk : Scheme.{u}) [IsIntegral Rk] :
    Spec (.of (Rk.residueField (genericPoint Rk))) ⟶ Rk :=
  Rk.fromSpecResidueField (genericPoint Rk)

def serreActualNativeOriginalSectionIncidence
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IA : Type u} [Fintype IA] [DecidableEq IA]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) : Scheme.{u} :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreThreePointSectionIncidence
    (serreActualNativeRankConfiguration p hp aRank) (hypersurfaceToBase p hp)
    (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank)
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)

def serreActualNativeOriginalSectionIncidenceToParameters
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IA : Type u} [Fintype IA] [DecidableEq IA]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    serreActualNativeOriginalSectionIncidence p hp e A aRank ⟶
      schemeModuleGlobalSectionsProjectiveParameters (hypersurfaceToBase p hp) e.E :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreThreePointSectionIncidenceToParameters
    (serreActualNativeRankConfiguration p hp aRank) (hypersurfaceToBase p hp)
    (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank)
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)

def serreActualNativeOriginalSectionIncidenceToConfiguration
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IA : Type u} [Fintype IA] [DecidableEq IA]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    serreActualNativeOriginalSectionIncidence p hp e A aRank ⟶ Rk :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreThreePointSectionIncidenceToConfiguration
    (serreActualNativeRankConfiguration p hp aRank) (hypersurfaceToBase p hp)
    (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank)
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)

def serreActualNativeOriginalSectionIncidenceMarkedOpen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IA : Type u} [Fintype IA] [DecidableEq IA]
    (A : SchemeModuleFiniteFreeAffineCover e.E IA)
    {Rk : Scheme.{u}}
    (aRank : Rk ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left) :
    (serreActualNativeOriginalSectionIncidence p hp e A aRank).Opens :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen
    (serreActualNativeRankConfiguration p hp aRank) (hypersurfaceToBase p hp)
    (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
    (serreActualNativeRankMarked p hp aRank)
    (serreActualNativeRankMarked_toBase p hp aRank)
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)

/-- Literal original selected-section Evidence, constructed by the accepted
native residue-parameter provider. The Evidence result is inferred directly. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeOriginalSelectedSectionEvidenceProvider
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
    (hmarked : s (IsLocalRing.closedPoint (Rk.residueField (genericPoint Rk))) ∈
      serreActualNativeOriginalSectionIncidenceMarkedOpen p hp e A aRank)
    (hcfg : s ≫ serreActualNativeOriginalSectionIncidenceToConfiguration p hp e A aRank =
      serreActualNativeOriginalResidueConfigurationPoint Rk)
    (n : Fin 3) :=
  serreActualCubicGroundFamily_nativeResidueParameterMarkedEvidenceProvider
    p hp hp0 a ha ι e C h9 A B aRank β G H hHG qF
    s hsp hmarked (serreActualNativeOriginalResidueConfigurationPoint Rk) hcfg n

end PfaffianDescent
