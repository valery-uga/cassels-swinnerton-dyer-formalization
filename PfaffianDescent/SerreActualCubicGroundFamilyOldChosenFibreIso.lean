import PfaffianDescent.SerreActualGroundFamilyOldMarkedSeed
import PfaffianDescent.SerreActualCubicGroundFamilyProjections
import AllCharacteristics.ProjectiveBaseChange

/-! The common old chosen fibre is the literal original canonical fibre,
using the actual Cartesian coefficient-cubic square internally. -/
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

@[irreducible]
def serreActualCubicGroundFamily_chosenOldFibreIso :=
  serreActualGroundFamily_coefficientChosenFibreIso
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b

@[irreducible]
def serreActualCubicGroundFamily_chosenOldFibreIso_hom_surface :=
  serreActualGroundFamily_coefficientChosenFibreIso_hom_surface
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b

@[irreducible]
def serreActualCubicGroundFamily_chosenOldFibreIso_hom_parameter :=
  serreActualGroundFamily_coefficientChosenFibreIso_hom_parameter
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b

/-- The actual old incidence seed fibre maps to the common old fibre at the
same ground parameter. Remaining arguments are cfg/marked/hm/s/hsp. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeedToCommonFibreIso :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreActualGroundFamily_oldSeedToCommonFibreIso (Cfg := Cfg)
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b

/-- The old marked incidence open internally supplies pointwise simple stalks
in the actual common old fibre. Remaining inputs are the structural incidence
seed and its parameter equality, then marked-open membership and index. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeed_commonMarked_stalk_isField :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreActualGroundFamily_oldSeed_commonMarked_stalk_isField (Cfg := Cfg)
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E)

/-- The old marked seed transport preserves the actual original cubic point;
its coefficient-cubic surface point is the genuine Cartesian lift. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSeedToCommonFibreIso_hom_surface :=
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  serreActualGroundFamily_oldSeedToCommonFibreIso_hom_surface (Cfg := Cfg)
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
    (A.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) e.E) b

end PfaffianDescent
