import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeProductChart

/-! # Common actual parameter coefficients and native evaluation functions -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {K : Type u} [Field K] {X B : Scheme.{u}}
variable (base : X ⟶ Spec (.of K)) (M : X.Modules)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (C : SchemeModuleFiniteFreeAffineCover M ι)
variable (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
variable (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
variable (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
variable (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))

def serreIncidenceGlobalBasisEvaluationMatrix :
    Matrix (Fin 3 × ι)
      (Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) Γ(B, ⊤) :=
  fun r k => (markedU r.1).appTop
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
      (BundleSectionZeroLocus.localFreeIsoOfOver (C.U (chart r.1)) ι (C.trivialization (chart r.1)))
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U (chart r.1))
        (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) r.2)

def serreIncidenceNativeParameterProductCoefficient
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(serreIncidenceNativeParameterProductChart base M b j, ⊤) :=
  (pullback.snd b (finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) j ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)).appTop
    ((Scheme.ΓSpecIso (.of (finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base M) j))).inv.hom
        (chartCoordinate (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) j k))

/-- The three actual product-chart factors have the same literal normalized
projective parameter coefficients. -/
theorem serreIncidenceNativeParameterProductMarked_coefficient (i : Fin 3)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j i).appTop
      (C.projectiveSectionLocalCoefficient base M (chart i,j) k) =
    serreIncidenceNativeParameterProductCoefficient base M b j k := by
  unfold SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalCoefficient
  have h := congrArg (fun t => t.appTop)
    (serreIncidenceNativeParameterProductMarked_parameter base M C b chart markedU hmarked j i)
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun t => t
    ((Scheme.ΓSpecIso (.of (finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base M) j))).inv.hom
        (chartCoordinate (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) j k))) h

/-- Each actual universal-chart scalar basis coefficient comes from the
actual configuration evaluation matrix, along its literal projection. -/
theorem serreIncidenceNativeParameterProductMarked_evaluation
    (r : Fin 3 × ι)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    serreUniversalChartEvaluationCoordinate base M C (chart r.1,j)
      (serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j r.1) r.2 k =
    (pullback.fst b (finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) j ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)).appTop
        (serreIncidenceGlobalBasisEvaluationMatrix base M C chart markedU r k) := by
  exact serreUniversalChartEvaluationCoordinate_eq_configuration base M C (chart r.1,j)
    (serreIncidenceNativeParameterProductMarked base M C b chart markedU hmarked j r.1)
    _ (markedU r.1)
    (serreIncidenceNativeParameterProductMarked_surface base M C b chart markedU hmarked j r.1)
    r.2 k

end
end PfaffianDescent
