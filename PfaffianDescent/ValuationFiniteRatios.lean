import Mathlib.RingTheory.Valuation.ValuationRing

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    {L : Type*} [Field L] [Algebra R L] [IsFractionRing R L]

/-- Among finitely many nonzero candidates, a valuation ring admits a denominator
relative to which every candidate is integral. -/
lemma valuation_finset_integral_ratios (s : Finset L) (hs : ∃ a ∈ s, a ≠ 0) :
    ∃ b ∈ s, b ≠ 0 ∧ ∀ a ∈ s, IsLocalization.IsInteger R (a / b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hs
  | @insert a s ha ih =>
    by_cases hS : ∃ b ∈ s, b ≠ 0
    · obtain ⟨b, hb, hb0, hbs⟩ := ih hS
      rcases ValuationRing.isInteger_or_isInteger R (a / b) with hab | hba
      · refine ⟨b, Finset.mem_insert_of_mem hb, hb0, ?_⟩
        intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hab
        · exact hbs c hc
      · rw [inv_div] at hba
        by_cases ha0 : a = 0
        · refine ⟨b, Finset.mem_insert_of_mem hb, hb0, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · simpa only [ha0, zero_div] using IsLocalization.isInteger_zero (R := R) (S := L)
          · exact hbs c hc
        · refine ⟨a, Finset.mem_insert_self _ _, ha0, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · simpa only [div_self ha0] using IsLocalization.isInteger_one (R := R) (S := L)
          · have he : c / a = (c / b) * (b / a) := by field_simp
            rw [he]
            exact IsLocalization.isInteger_mul (hbs c hc) hba
    · have ha0 : a ≠ 0 := by
        obtain ⟨c, hc, hc0⟩ := hs
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hc0
        · exact False.elim (hS ⟨c, hc, hc0⟩)
      refine ⟨a, Finset.mem_insert_self _ _, ha0, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · simpa only [div_self ha0] using IsLocalization.isInteger_one (R := R) (S := L)
      · have hc0 : c = 0 := by by_contra h; exact hS ⟨c, hc, h⟩
        simpa only [hc0, zero_div] using IsLocalization.isInteger_zero (R := R) (S := L)

/-- A finite family of fractions with at least one nonzero member has an integral normalization. -/
theorem valuation_finite_integral_ratios {I : Type*} [Fintype I] (c : I → L)
    (hc : ∃ i, c i ≠ 0) :
    ∃ i, c i ≠ 0 ∧ ∀ j, IsLocalization.IsInteger R (c j / c i) := by
  classical
  have hs : ∃ a ∈ Finset.univ.image c, a ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    exact ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
  obtain ⟨b, hb, hb0, h⟩ := valuation_finset_integral_ratios R _ hs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨i, hb0, fun j => h _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)⟩

end
end PfaffianDescent
