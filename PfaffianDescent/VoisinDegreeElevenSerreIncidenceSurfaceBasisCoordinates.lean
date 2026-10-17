import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionBasisPullback
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalBasisCoordinates

/-! # Actual surface coordinates of reconstructed global sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma serreIncidenceSectionCoordinate_postcompose
    {X : Scheme.{u}} {M N : X.Modules} (ι : Type u) [Fintype ι] [DecidableEq ι]
    (t : SheafOfModules.free (R := X.ringCatSheaf) ι ≅ M)
    (A : M ≅ N) (s : M.sections) (i : ι) :
    sectionCoordinateOfFreeIso ι (t ≪≫ A) (SheafOfModules.sectionsMap A.hom s) i =
      sectionCoordinateOfFreeIso ι t s i := by
  have h := module_coordinate_postcompose ι t A (schemeModuleSectionsEquivTop M s) i
  have hs : schemeModuleSectionsEquivTop N (SheafOfModules.sectionsMap A.hom s) =
      (A.hom.val.app (Opposite.op ⊤)).hom (schemeModuleSectionsEquivTop M s) := rfl
  rw [← hs] at h
  simp only [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    Equiv.symm_apply_apply] at h
  exact h

lemma serreIncidenceSurfaceSectionCoordinate_pullback
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) ι ≅
      (Scheme.Modules.overEquiv U).functor.obj (M.over U))
    (s : M.sections) (i : ι) :
    sectionCoordinateOfFreeIso ι (t ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M))
      (pullbackSection U.ι M (isIso_pullbackUnitComparison U.ι) s) i =
      sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U s) i := by
  let A := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  have hs : SheafOfModules.sectionsMap A.hom (restrictSectionToOpen U s) =
      pullbackSection U.ι M (isIso_pullbackUnitComparison U.ι) s := by
    rw [Iso.trans_hom, SheafOfModules.sectionsMap_comp, serreIncidenceOverSection_restrict]
    exact restrictModuleSection_to_pullbackSection U.ι _ s
  rw [← hs]
  exact serreIncidenceSectionCoordinate_postcompose ι t A _ i

/-- Actual restricted section coordinates satisfy actual finite-basis
reconstruction as regular functions on the surface chart. -/
theorem serreIncidenceSurfaceBasisCoordinate_reconstruct
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (U : X.Opens) (ι : Type u) [Fintype ι] [DecidableEq ι]
    (t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) ι ≅
      (Scheme.Modules.overEquiv U).functor.obj (M.over U))
    (s : SchemeModuleGlobalSectionsOver base M) (a : ι) :
    (∑ k, U.ι.appTop (affineFunctionHom base
        ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)) *
      sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
        (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) a) =
    sectionCoordinateOfFreeIso ι t (restrictSectionToOpen U
      (schemeModuleGlobalSectionsOverEquivSections base M s)) a := by
  let A := (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  have h := sectionCoordinateOfFreeIso_parameterizedSchemeModuleSection base M U.ι
    (fun k => U.ι.appTop (affineFunctionHom base
      ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)))
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)) ι (t ≪≫ A) a
  rw [serreIncidenceParameterizedBasis_eq_pullback] at h
  have hsum := Finset.sum_congr
    (show (Finset.univ : Finset (Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M)))) = Finset.univ from rfl) (fun k _ =>
    congrArg (fun z => U.ι.appTop (affineFunctionHom base
      ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)) * z)
      (serreIncidenceSurfaceSectionCoordinate_pullback U M ι t
        (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)) a))
  exact hsum.symm.trans (h.symm.trans
    (serreIncidenceSurfaceSectionCoordinate_pullback U M ι t
      (schemeModuleGlobalSectionsOverEquivSections base M s) a))

end PfaffianDescent
