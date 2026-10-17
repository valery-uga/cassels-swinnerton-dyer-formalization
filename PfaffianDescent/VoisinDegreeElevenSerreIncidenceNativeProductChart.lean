import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProductChartMaps
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceUniversalEvaluationTransport

/-! # Actual product charts of the bundle section incidence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {K : Type u} [Field K] {X B : Scheme.{u}}
variable (base : X ⟶ Spec (.of K)) (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable {ι : Type u} (C : SchemeModuleFiniteFreeAffineCover M ι)
variable (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
variable (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
variable (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
variable (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))

abbrev serreIncidenceNativeParameterProductChart : Scheme.{u} :=
  pullback b (finiteDimensionalProjectiveChartι K
    (SchemeModuleGlobalSectionsOver base M) j ≫
    schemeModuleGlobalSectionsProjectiveParametersToBase base M)

/-- Every marked product-chart factor is built from the actual configuration
marked map and the common normalized section parameter projection. -/
def serreIncidenceNativeParameterProductMarked (i : Fin 3) :
    serreIncidenceNativeParameterProductChart base M b j ⟶
      (C.projectiveSectionOpenCover base M).X (chart i, j) :=
  serreIncidenceProductChartMarked b base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j)
    (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
    (fun i => (C.U (chart i) : Scheme.{u}))
    (fun i => (C.U (chart i)).ι) markedU (fun _ => rfl) i

@[reassoc]
theorem serreIncidenceNativeParameterProductMarked_surface (i : Fin 3) :
    serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i ≫
      C.projectiveSectionOpenCoverToSurfaceChart base M (chart i, j) =
    pullback.fst b (finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) j ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ markedU i :=
  serreIncidenceProductChartMarked_fst _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
theorem serreIncidenceNativeParameterProductMarked_parameter (i : Fin 3) :
    serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i ≫
      C.projectiveSectionOpenCoverToParameterChart base M (chart i, j) =
    pullback.snd b (finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) j ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  serreIncidenceProductChartMarked_snd _ _ _ _ _ _ _ _ _ _ _

/-- The internally constructed factors satisfy the literal global incidence
triangle, so their local ideal equations are equations of the actual
three-point incidence scheme. -/
theorem serreIncidenceNativeParameterProductMarked_incidence (i : Fin 3) :
    serreIncidenceProductChartToProduct b
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j) ≫
    fixedLinearSystemIncidenceMap b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked i =
    serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i ≫
      (C.projectiveSectionOpenCover base M).f (chart i, j) := by
  have h := serreIncidenceProductChartMarked_comp b base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j)
    (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
    (fun i => (C.U (chart i) : Scheme.{u}))
    (fun i => (C.U (chart i)).ι) markedU (fun _ => rfl) i
  change _ = serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i ≫
    pullback.map ((C.U (chart i)).ι ≫ base)
      (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j ≫
        schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      base (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      (C.U (chart i)).ι
      (finiteDimensionalProjectiveChartι K (SchemeModuleGlobalSectionsOver base M) j)
      (𝟙 _) (by simp) (by simp)
  exact h.symm

end
end PfaffianDescent
