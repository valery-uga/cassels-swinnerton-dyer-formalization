import PfaffianDescent.IncidenceChartKernelSheaf
import PfaffianDescent.GrassmannianChartSectionFunctions
import PfaffianDescent.SheafKernelComparison

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (K : Type u) [CommRing K] {X : Scheme.{u}}
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (f g : X ⟶ grassmannianChartScheme K 3 3)
    (h : f ≫ grassmannianChartι K σ = g ≫ grassmannianChartι K τ)
include h

/-- On a chart overlap, the two actual sheaf restriction maps have identical section kernels. -/
lemma incidenceGraphRestrictionSheaf_overlap_kernels (U : X.Opens) :
    ((incidenceGraphRestrictionSheaf X σ (grassmannianChartFunctions K f)).val.app (op U)).hom.ker =
      ((incidenceGraphRestrictionSheaf X τ (grassmannianChartFunctions K g)).val.app (op U)).hom.ker := by
  have hW : grassmannianChartSubmodule Γ(X, U) σ
      ((grassmannianChartFunctions K f).map (regularFunctionRestrict X U)) =
      grassmannianChartSubmodule Γ(X, U) τ
      ((grassmannianChartFunctions K g).map (regularFunctionRestrict X U)) :=
    grassmannianChartSectionFunctions_submodule_eq K σ τ f g h U
  have hk : (incidenceRestrictionMap Γ(X, U) σ
      ((grassmannianChartFunctions K f).map (regularFunctionRestrict X U))).ker =
      (incidenceRestrictionMap Γ(X, U) τ
      ((grassmannianChartFunctions K g).map (regularFunctionRestrict X U))).ker := by
    ext c
    change incidenceRestrictionMap Γ(X, U) σ _ c = 0 ↔ incidenceRestrictionMap Γ(X, U) τ _ c = 0
    rw [incidenceRestrictionMap_eq_zero_iff, incidenceRestrictionMap_eq_zero_iff, hW]
  exact (congrArg LinearMap.ker (incidenceGraphRestrictionSheaf_sections X σ
    (grassmannianChartFunctions K f) U)).trans
      (hk.trans (congrArg LinearMap.ker (incidenceGraphRestrictionSheaf_sections X τ
        (grassmannianChartFunctions K g) U)).symm)

/-- The actual free kernel sheaves agree on all overlaps, through their ambient coefficient sheaf. -/
noncomputable def incidenceGraphKernelSheafOverlapIso :
    kernel (incidenceGraphRestrictionSheaf X σ (grassmannianChartFunctions K f)) ≅
      kernel (incidenceGraphRestrictionSheaf X τ (grassmannianChartFunctions K g)) :=
  sheafKernelIsoOfEqualSections X.ringCatSheaf _ _
    (fun U => incidenceGraphRestrictionSheaf_overlap_kernels K σ τ f g h U.unop)

lemma incidenceGraphKernelSheafOverlapIso_hom_ι :
    (incidenceGraphKernelSheafOverlapIso K σ τ f g h).hom ≫
      kernel.ι (incidenceGraphRestrictionSheaf X τ (grassmannianChartFunctions K g)) =
      kernel.ι (incidenceGraphRestrictionSheaf X σ (grassmannianChartFunctions K f)) :=
  sheafKernelIsoOfEqualSections_hom_ι X.ringCatSheaf _ _ _

end
end PfaffianDescent
