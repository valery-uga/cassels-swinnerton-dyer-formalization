import PfaffianDescent.SerreActualGroundFamilyChosenMarkedSeed
import PfaffianDescent.SerreActualCubicGroundFamilyParameterChange
import PfaffianDescent.SerreActualCubicGroundFamilyProjections

/-! Three old common-fibre marked sections construct an actual new incidence
seed on the literal coefficient-cubic Serre module and SAME chosen ground
parameter. No new incidenceMarkedOpen or geometry certificate is supplied. -/
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
variable {U : Scheme.{u}}
variable (b : U ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))


@[irreducible]
def serreActualCubicGroundFamily_chosenMarkedSeed :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
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
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b

@[irreducible]
def serreActualCubicGroundFamily_chosenMarkedSeed_toParameters :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
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
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b

@[irreducible]
def serreActualCubicGroundFamily_chosenMarkedSeed_surface :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
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
    (serreActualCubicGroundFamily_global_zero_comparison p hp e C h9 A B G H hHG) b

end PfaffianDescent
