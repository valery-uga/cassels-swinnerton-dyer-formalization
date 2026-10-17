import PfaffianDescent.VoisinProjectiveChartPullbackCoordinates
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOverSection
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceRelativeEvaluation

/-! # Actual global basis coordinates on universal product charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceOverSection_restrict
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (s : M.sections) :
    SheafOfModules.sectionsMap ((Scheme.Modules.overFunctorEquiv U).app M).hom
      (restrictSectionToOpen U s) = restrictModuleSection U.ι M s := by
  apply (M.restrict U.ι).unitHomEquiv.symm.injective
  rw [← (((Scheme.Modules.overEquiv U).functor.obj (M.over U))).unitHomEquiv_symm_comp]
  unfold restrictModuleSection
  rw [Equiv.symm_apply_apply]
  exact cubicClosedPointSerreFiniteZeroResidual_over_section_hom U M s

theorem serreIncidenceOverSection_pullback
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (s : M.sections) :
    let B := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
    SheafOfModules.sectionsMap B.inv
      (pullbackSection U.ι M (isIso_pullbackUnitComparison U.ι) s) =
      restrictSectionToOpen U s := by
  dsimp only
  let B := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  have h : SheafOfModules.sectionsMap B.hom (restrictSectionToOpen U s) =
      pullbackSection U.ι M (isIso_pullbackUnitComparison U.ι) s := by
    rw [Iso.trans_hom, SheafOfModules.sectionsMap_comp, serreIncidenceOverSection_restrict]
    exact restrictModuleSection_to_pullbackSection U.ι _ s
  rw [← h, ← SheafOfModules.sectionsMap_comp, B.hom_inv_id,
    SheafOfModules.sectionsMap_id]

/-- Each actual universal-chart basis coordinate is pulled from the actual
restriction of that global section on its surface trivialization. -/
theorem serreIncidenceUniversalBasisCoordinate_eq_surface
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (s : M.sections) (i : ι) :
    sectionCoordinateOfFreeIso ι (C.projectiveSectionLocalFreeIso base M ij)
      (pullbackSection (C.projectiveSectionOpenCoverToSurface base M ij) M
        (isIso_pullbackUnitComparison _) s) i =
    (C.projectiveSectionOpenCoverToSurfaceChart base M ij).appTop
      (sectionCoordinateOfFreeIso ι
        (localFreeIsoOfOver (C.U ij.1) ι (C.trivialization ij.1))
        (restrictSectionToOpen (C.U ij.1) s) i) := by
  have hcoord := C.projectiveSectionLocalFreeIso_coordinate_pullback base M ij
    (restrictSectionToOpen (C.U ij.1) s) i
  have hsection := C.projectiveSectionLocalSection_globalPullback base M ij s
  dsimp only at hcoord hsection
  rw [serreIncidenceOverSection_pullback] at hsection
  simp only [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    Equiv.symm_apply_apply] at hcoord
  rw [hsection] at hcoord
  exact hcoord

end PfaffianDescent
