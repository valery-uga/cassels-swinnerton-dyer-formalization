import AllCharacteristics.FreeActionTensorKernels

/-! # Detecting the affine fixed-locus ideal by actual field-valued maps -/

namespace AllCharacteristics
universe u v
variable (B : Type u) [CommRing B]
variable (G : Type v) [Group G] [MulSemiringAction G B]

/-- A proper action-difference ideal produces an actual fixed map to a field.
The residue field is constructed from a maximal ideal containing that ideal. -/
theorem exists_fixed_field_map_of_actionDifferenceIdeal_ne_top (g : G)
    (hne : actionDifferenceIdeal B G g ≠ ⊤) :
    ∃ (K : Type u) (_ : Field K) (a : B →+* K),
      a.comp (MulSemiringAction.toRingHom G B g) = a := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (actionDifferenceIdeal B G g) hne
  let : M.IsMaximal := hM
  let K := B ⧸ M
  refine ⟨K, Ideal.Quotient.field M, Ideal.Quotient.mk M, ?_⟩
  apply RingHom.ext
  intro b
  have hm : b - g • b ∈ M := hle (Ideal.subset_span ⟨b, rfl⟩)
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- Absence of fixed field-valued maps forces the actual affine fixed locus to be empty. -/
theorem actionDifferenceIdeal_eq_top_of_no_fixed_field_maps (g : G)
    (h : ∀ (K : Type u) [Field K] (a : B →+* K),
      a.comp (MulSemiringAction.toRingHom G B g) ≠ a) :
    actionDifferenceIdeal B G g = ⊤ := by
  by_contra hne
  obtain ⟨K, hK, a, ha⟩ := exists_fixed_field_map_of_actionDifferenceIdeal_ne_top B G g hne
  let : Field K := hK
  exact h K a ha

end AllCharacteristics
