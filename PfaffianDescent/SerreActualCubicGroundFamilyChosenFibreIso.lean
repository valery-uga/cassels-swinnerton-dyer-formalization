import PfaffianDescent.SerreActualGroundFamilyChosenFibreIso
import PfaffianDescent.SerreActualCubicGroundFamilyParameterChange
import PfaffianDescent.SerreActualCubicGroundFamilyProjections
import PfaffianDescent.SerreActualClosedPullbackZeroMarkedFibre

/-! The same chosen ground parameter gives the literal coefficient-cubic
canonical zero fibre. This compares fibres over the actual new surface. -/
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

/-- Actual common new fibre identified with the literal canonical universal
zero fibre at the unchanged chosen ground parameter. -/
@[irreducible]
def serreActualCubicGroundFamily_chosenNewFibreIso :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  serreActualGroundFamily_chosenFibreIso
    x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
    (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
    (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
    (B.projectiveSectionLocalZeroGluedToAmbient x M) b

/-- The canonical fibre identification preserves the actual coefficient-cubic
surface, so the marked points are the same geometric points. -/
@[irreducible]
def serreActualCubicGroundFamily_chosenNewFibreIso_hom_surface :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  serreActualGroundFamily_chosenFibreIso_hom_surface
    x (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
    (schemeModuleGlobalSectionsProjectiveParametersToBase x M)
    (serreActualCubicGroundKernelParameters p hp e C h9 G H hHG)
    (serreActualCubicGroundKernelParameters_toBase p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_surface p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG)
    (B.projectiveSectionLocalZeroGluedToAmbient x M) b

/-- Actual old common fibre compared directly with the literal new canonical
zero fibre. The ideal equality and both surface/parameter projections are
supplied internally by the checked native family comparisons. -/
@[irreducible]
def serreActualCubicGroundFamily_chosenOldToCanonicalNewIso :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  (serreActualCubicGroundFamily_parameterChangeIso p hp e C h9 A B G H hHG b).symm.trans
    (serreActualCubicGroundFamily_chosenNewFibreIso p hp e C h9 B G H hHG b)

/-- A field stalk at an actual old marked point transfers to the literal new
canonical zero fibre at the same ground parameter, pointwise only. -/
@[irreducible]
def serreActualCubicGroundFamily_chosenOldMarked_stalk_isField :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  letI := A.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (hypersurfaceToBase p hp) e.E
  letI := B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient x M
  serreActualChosenFibreIso_stalk_isField
    (serreActualCubicGroundFamily_chosenOldToCanonicalNewIso p hp e C h9 A B G H hHG b)

end PfaffianDescent
