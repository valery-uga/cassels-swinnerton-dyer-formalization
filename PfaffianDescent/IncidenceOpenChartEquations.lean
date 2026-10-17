import PfaffianDescent.IncidenceOpenChartSubmodule
import PfaffianDescent.IncidenceFiberLinearNaturality
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (R : Type*) [CommRing R]

lemma incidenceRestrictionMap_zero_iff_submodule
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T T' : Matrix (Fin 3) (Fin 3) R)
    (hW : grassmannianChartSubmodule R σ T = grassmannianChartSubmodule R τ T')
    (c : AlternatingTripleIndex → R) :
    incidenceRestrictionMap R σ T c = 0 ↔ incidenceRestrictionMap R τ T' c = 0 := by
  rw [incidenceRestrictionMap_eq_zero_iff, incidenceRestrictionMap_eq_zero_iff, hW]

end
section
variable (K : Type u) [CommRing K]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U : (grassmannianScheme K 3 3).Opens) (hU : U ≤ (grassmannianChartι K σ).opensRange)

/-- Inside any one chart, the global simultaneous equations reduce to that chart's actual restriction kernel. -/
lemma mem_incidenceEquationSections_open_chart
    (c : AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U)) :
    c ∈ incidenceEquationSections K U ↔
      incidenceRestrictionMap Γ(grassmannianScheme K 3 3, U) σ (incidenceOpenChartMatrix K σ U hU) c = 0 := by
  rw [mem_incidenceEquationSections]
  have he (τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
      incidenceRestrictionMap _ σ
          ((incidenceOpenChartMatrix K σ U hU).map ((grassmannianChartι K τ).app U).hom)
          (((grassmannianChartι K τ).app U).hom ∘ c) = 0 ↔
        (incidenceChartRestrictionSheafMap K τ).val.app (op U) c = 0 := by
    rw [incidenceChartRestrictionSheafMap_sections]
    exact incidenceRestrictionMap_zero_iff_submodule _ σ τ _ _
      (incidenceOpenChartSubmodule K σ U hU τ) _
  constructor
  · intro h
    have hs := (he σ).mpr (h σ)
    have hm := incidenceRestrictionMap_map ((grassmannianChartι K σ).app U).hom σ
      (incidenceOpenChartMatrix K σ U hU) c
    haveI : IsIso ((grassmannianChartι K σ).app U) := Scheme.Hom.isIso_app _ U hU
    have hi := ((ConcreteCategory.isIso_iff_bijective ((grassmannianChartι K σ).app U)).mp inferInstance).1
    funext i
    apply hi
    exact ((congrFun hm i).symm.trans (congrFun hs i)).trans (map_zero _).symm
  · intro h τ
    apply (he τ).mp
    rw [incidenceRestrictionMap_map, h]
    funext i
    exact map_zero _

lemma incidenceEquationSections_eq_open_chart :
    incidenceEquationSections K U =
      (incidenceRestrictionMap Γ(grassmannianScheme K 3 3, U) σ (incidenceOpenChartMatrix K σ U hU)).ker := by
  ext c
  exact mem_incidenceEquationSections_open_chart K σ U hU c

/-- Sections of the actual global incidence sheaf on a chart have exactly thirty-six free coordinates. -/
noncomputable def incidenceKernelSheafOpenSectionsEquiv :
    Γ(incidenceKernelSheaf K, U) ≃ₗ[Γ(grassmannianScheme K 3 3, U)]
      (IncidenceFiberIndex → Γ(grassmannianScheme K 3 3, U)) :=
  (incidenceKernelSheafSectionsEquiv K U).trans
    ((LinearEquiv.ofEq _ _ (incidenceEquationSections_eq_open_chart K σ U hU)).trans
      (incidenceRestrictionFiberEquiv _ σ (incidenceOpenChartMatrix K σ U hU)))

lemma incidenceKernelSheafOpenSectionsEquiv_apply (x : Γ(incidenceKernelSheaf K, U)) :
    incidenceKernelSheafOpenSectionsEquiv K σ U hU x =
      incidenceFiberProjection _ σ (incidenceOpenChartMatrix K σ U hU)
        ((incidenceKernelSheafι K).val.app (op U) x) := by
  let c := (LinearEquiv.ofEq _ _ (incidenceEquationSections_eq_open_chart K σ U hU))
    (incidenceKernelSheafSectionsEquiv K U x)
  exact (incidenceFiberProjection_kernel _ σ (incidenceOpenChartMatrix K σ U hU) c).symm.trans
    (congrArg (incidenceFiberProjection _ σ (incidenceOpenChartMatrix K σ U hU))
      (incidenceKernelSheafSectionsEquiv_val K U x))

end
end PfaffianDescent
