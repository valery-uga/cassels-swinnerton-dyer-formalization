import PfaffianDescent.SerreActualParameterizedSectionPullback
import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

/-! The actual normalized universal section, pulled to a common chart,
is the canonical linear combination with the actual pulled coefficients. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualLocalUniversalSection_pullbackComp
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (q : T ⟶ X) (h : f ≫ C.projectiveSectionOpenCoverToSurface base M ij = q) :
    SheafOfModules.sectionsMap
        (((Scheme.Modules.pullbackComp f
            (C.projectiveSectionOpenCoverToSurface base M ij)).app M ≪≫
          (Scheme.Modules.pullbackCongr h).app M).hom)
        (pullbackSection f (C.projectiveSectionLocalModule base M ij)
          (isIso_pullbackUnitComparison f)
          (C.projectiveSectionLocalUniversalSection base M ij)) =
      parameterizedSchemeModuleSection base M q
        (fun i => f.appTop (C.projectiveSectionLocalCoefficient base M ij i))
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)) := by
  exact serreActualParameterizedSection_pullbackComp base M
    (C.projectiveSectionOpenCoverToSurface base M ij) f q h
    (C.projectiveSectionLocalCoefficient base M ij)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

end PfaffianDescent
