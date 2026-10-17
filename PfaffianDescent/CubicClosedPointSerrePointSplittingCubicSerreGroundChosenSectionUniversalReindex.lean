import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionFiniteReindex
import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal old universal chart section, in the canonical rank-indexed
basis, with its actual coefficients reindexed by the inverse finCongr. -/
theorem pointSplittingCubicSerreGroundChosenSection_localUniversalSection_reindex
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    {n : ℕ} (hn : Module.finrank K (SchemeModuleGlobalSectionsOver base M) = n) :
    C.projectiveSectionLocalUniversalSection base M ij =
      parameterizedSchemeModuleSection (K := K) (ι := Fin n) base M
        (C.projectiveSectionOpenCoverToSurface base M ij)
        (fun j => C.projectiveSectionLocalCoefficient base M ij ((finCongr hn).symm j))
        (fun j => Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base M) hn j) := by
  unfold SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalUniversalSection
  simpa only [Module.finBasisOfFinrankEq, Module.Basis.reindex_apply] using
    pointSplittingCubicSerreGroundChosenSection_parameterizedSection_reindex
      base M (finCongr hn) (C.projectiveSectionOpenCoverToSurface base M ij)
      (C.projectiveSectionLocalCoefficient base M ij)
      (fun i => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)

end PfaffianDescent
