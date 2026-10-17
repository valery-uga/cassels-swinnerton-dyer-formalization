import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionUniversalReindex
import PfaffianDescent.SerreActualParameterizedSectionPullback

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal local universal section, pulled to any common source and
transported through the actual PBComp/PBCongr, is the canonical rank-indexed
parameterized section with the actual pulled regular coefficients. -/
theorem pointSplittingCubicSerreGroundChosenSection_localUniversalSection_pullback_reindex
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    {n : ℕ} (hn : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = n)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (q : T ⟶ X) (h : f ≫ C.projectiveSectionOpenCoverToSurface base M ij = q) :
    SheafOfModules.sectionsMap
      (((Scheme.Modules.pullbackComp f (C.projectiveSectionOpenCoverToSurface base M ij)).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).hom)
      (pullbackSection f (C.projectiveSectionLocalModule base M ij)
        (isIso_pullbackUnitComparison f)
        (C.projectiveSectionLocalUniversalSection base M ij)) =
    parameterizedSchemeModuleSection (K := K) (ι := Fin n) base M q
      (fun j => f.appTop
        (C.projectiveSectionLocalCoefficient base M ij ((finCongr hn).symm j)))
      (fun j => Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base M) hn j) := by
  rw [pointSplittingCubicSerreGroundChosenSection_localUniversalSection_reindex base M C ij hn]
  exact serreActualParameterizedSection_pullbackComp base M
    (C.projectiveSectionOpenCoverToSurface base M ij) f q h
    (fun j => C.projectiveSectionLocalCoefficient base M ij ((finCongr hn).symm j))
    (fun j => Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base M) hn j)

end PfaffianDescent
