import PfaffianDescent.SerreActualCubicGroundFamilyChosenMarkedSeed
import PfaffianDescent.SerreActualGroundFamilyOldMarkedSections
import AllCharacteristics.ProjectiveBaseChange

/-! An actual old incidence seed gives the actual new selected incidence
seed, with all three vanishing marked lifts constructed internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (A : SchemeModuleFiniteFreeAffineCover e.E I)
variable (B : SchemeModuleFiniteFreeAffineCover
  ((Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
variable (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
variable (hHG : H * G = 1)
variable {U Cfg : Scheme.{u}}
variable (b : U ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))



/-- Remaining arguments cfg/marked/hm/s/hsp are structural actual old seed
data. No new incidence-open membership or section-vanishing comparison is
assumed. The ground parameter and coefficient-cubic Serre module are fixed. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeed_toNewMarkedSeed :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  fun (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : U ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      b ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG) =>
    let m := serreActualGroundFamily_oldSeed_commonMarkedSection
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    let hmNew := serreActualGroundFamily_oldSeed_commonMarkedSection_toParameter
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    serreActualGroundFamily_chosenMarkedSeed
      x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
      (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
      (B.projectiveSectionLocalZeroGluedToAmbient x M)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b m hmNew

/-- Remaining arguments cfg/marked/hm/s/hsp are structural actual old seed
data. No new incidence-open membership or section-vanishing comparison is
assumed. The ground parameter and coefficient-cubic Serre module are fixed. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeed_toNewMarkedSeed_toParameters :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  fun (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : U ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      b ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG) =>
    let m := serreActualGroundFamily_oldSeed_commonMarkedSection
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    let hmNew := serreActualGroundFamily_oldSeed_commonMarkedSection_toParameter
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    serreActualGroundFamily_chosenMarkedSeed_toParameters
      x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
      (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
      (B.projectiveSectionLocalZeroGluedToAmbient x M)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b m hmNew

/-- Remaining arguments cfg/marked/hm/s/hsp are structural actual old seed
data. No new incidence-open membership or section-vanishing comparison is
assumed. The ground parameter and coefficient-cubic Serre module are fixed. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeed_toNewMarkedSeed_surface :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  fun (cfg : Cfg ⟶ Spec (.of K))
    (marked : Fin 3 → (Cfg ⟶ hypersurface p hp))
    (hm : ∀ i, marked i ≫ hypersurfaceToBase p hp = cfg)
    (s : U ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E))
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp)
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      marked hm (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) =
      b ≫ serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG) =>
    let m := serreActualGroundFamily_oldSeed_commonMarkedSection
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    let hmNew := serreActualGroundFamily_oldSeed_commonMarkedSection_toParameter
      (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E)
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
      (isPullback_projectiveCoefficientMap (algebraMap K F) (equationIdeal p hp)
        (equationIdeal (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (equationIdeal_map (algebraMap K F) p hp))
      (serreActualGroundPlaneOriginalParameters (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualGroundPlaneOriginalParameters_toBase (hypersurfaceToBase p hp) e.E h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_surface p hp e h9 G H hHG)
      (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b cfg marked hm s hsp
    serreActualGroundFamily_chosenMarkedSeed_surface_fromOld
      x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
      (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
      (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
      (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
      (B.projectiveSectionLocalZeroGluedToAmbient x M)
      (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
      (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)
      (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b m hmNew

end PfaffianDescent
