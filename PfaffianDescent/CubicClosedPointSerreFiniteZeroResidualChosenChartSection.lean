import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundSectionGraph

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def cubicClosedPointSerreFiniteZeroResidual_chosenChartSection
    {K : Type u} [Field K] {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K) :
    SchemeModuleGlobalSectionsOver base M :=
  (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr.symm
    (Finsupp.equivFunOnFinite.symm (fun k =>
      b (chartCoordinate (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k)))

@[simp]
theorem cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_coordinates
    {K : Type u} [Field K] {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr
      (cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b) k =
      b (chartCoordinate (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k) := by
  simp [cubicClosedPointSerreFiniteZeroResidual_chosenChartSection]

theorem cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_nonzero
    {K : Type u} [Field K] {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K) :
    cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b ≠ 0 := by
  intro h
  have hc := cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_coordinates base M j b j
  rw [h, map_zero, Finsupp.zero_apply, chartCoordinate_self, map_one] at hc
  exact zero_ne_one hc

theorem cubicClosedPointSerreFiniteZeroResidual_chosenParameter_exists_section
    {K : Type u} [Field K] {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M)
    (ht : t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _) :
    ∃ (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
      (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K),
      b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K ∧
      serreIncidenceGroundSectionParameter base M j b = t ∧
      cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b ≠ 0 := by
  obtain ⟨j,b,hb,hbt⟩ := exists_finiteDimensionalProjectiveChart_hom_eq_of_fieldPoint
    (RingHom.id K) t (by simpa [schemeModuleGlobalSectionsProjectiveParametersToBase] using ht)
  exact ⟨j,b,hb,hbt,cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_nonzero base M j b⟩

end PfaffianDescent
