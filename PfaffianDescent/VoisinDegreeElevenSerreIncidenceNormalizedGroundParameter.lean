import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSectionParameter

/-! # Internally normalized ground section parameters and their actual sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Choose an actual ground section chart and an invertible scalar so its
literal chart coordinates are exactly the actual basis coordinates of the
scaled original section. -/
theorem serreIncidenceSection_exists_normalized_ground_parameter
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (s : SchemeModuleGlobalSectionsOver base M) (hs : s ≠ 0) :
    ∃ (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
      (b : finiteDimensionalProjectiveChartRing K
        (SchemeModuleGlobalSectionsOver base M) j →+* K) (a : K),
      IsUnit a ∧
      b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K ∧
      ∀ k, b (chartCoordinate (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k) =
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr (a • s) k := by
  obtain ⟨j, b, t, hj, hb, hbt, hc, ht⟩ :=
    serreIncidenceSection_exists_native_parameter (L := K) base M s hs
  have hj' : (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s j ≠ 0 := by
    simpa using hj
  refine ⟨j, b,
    ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s j)⁻¹,
    isUnit_iff_ne_zero.mpr (inv_ne_zero hj'), ?_, ?_⟩
  · simpa using hb
  · intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    simpa using hc k

end PfaffianDescent
