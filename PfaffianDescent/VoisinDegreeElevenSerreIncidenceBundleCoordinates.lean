import PfaffianDescent.VoisinGenericPullbackCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAffineMatrix

/-! # Native bundle-coordinate pullback for incidence evaluation -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The free coordinate of the actual pulled-back bundle section is the
actual pullback of its regular coordinate function, for an arbitrary scheme
morphism.  This compares the incidence equations with the relative matrix. -/
theorem serreIncidenceSectionCoordinate_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ι : Type u) [Fintype ι] [DecidableEq ι]
    (M : Y.Modules) (t : SheafOfModules.free (R := Y.ringCatSheaf) ι ≅ M)
    (s : M.sections) (i : ι) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
      (BundleSectionZeroLocus.pullbackFreeIso f ι t)
      (BundleSectionZeroLocus.pullbackSection f M
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison f) s) i =
    f.appTop (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι t s i) := by
  have h := BundleSectionZeroLocus.moduleOpenTopLinearEquivOfPullbackFreeIso_general
    f ι M t (schemeModuleSectionsEquivTop M s) i
  dsimp only at h
  simp only [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    Equiv.symm_apply_apply] at h
  exact h

/-- The native nine-section frame agrees with the actual universal-section
basis after the literal index equivalence induced by finrank nine. -/
theorem serreIncidenceNineGlobalSections_eq_finBasis
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X N)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9) (j : Fin 9) :
    serreIncidenceNineGlobalSections base e h9 j =
      schemeModuleGlobalSectionsOverEquivSections base (show X.Modules from e.E)
        (Module.finBasis F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))
          ((finCongr h9).symm j)) := by
  simp only [serreIncidenceNineGlobalSections, Module.finBasisOfFinrankEq,
    Module.Basis.reindex_apply, schemeModuleGlobalSectionsOverEquivSections]
  rfl

end PfaffianDescent
