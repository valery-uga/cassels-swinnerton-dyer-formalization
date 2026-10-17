import PfaffianDescent.QuinticPowerBasis
import Mathlib.Algebra.CharZero.Infinite

namespace PfaffianDescent
open Module IntermediateField
open scoped BigOperators

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- A primitive generator of a two-generated separable extension can be chosen
as a ground-field linear combination of the two given generators. The finite
intermediate-field argument is adapted from mathlib's primitive-element proof. -/
theorem primitive_linear_combination (a b : L) :
    ∃ t : K, K⟮a, b⟯ = K⟮a + t • b⟯ := by
  let : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L
      (Field.exists_primitive_element K L)
  let f : K → IntermediateField K L := fun t => K⟮a + t • b⟯
  obtain ⟨x, y, hxy, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x, le_antisymm ?_ ?_⟩
  · have hx : a + x • b ∈ K⟮a + x • b⟯ := mem_adjoin_simple_self K _
    have hy : a + y • b ∈ K⟮a + x • b⟯ := by
      rw [show K⟮a + x • b⟯ = K⟮a + y • b⟯ from heq]
      exact mem_adjoin_simple_self K _
    have hb := (K⟮a + x • b⟯).sub_mem hx hy
    rw [show (a + x • b) - (a + y • b) = (x - y) • b by rw [sub_smul]; abel] at hb
    have hb' := (K⟮a + x • b⟯).smul_mem hb (x := (x - y)⁻¹)
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hxy), one_smul] at hb'
    have ha : a ∈ K⟮a + x • b⟯ := by
      simpa only [add_sub_cancel_right] using
        (K⟮a + x • b⟯).sub_mem hx ((K⟮a + x • b⟯).smul_mem hb' (x := x))
    rw [adjoin_le_iff]
    rintro z (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    exact (K⟮a, b⟯).add_mem (mem_adjoin_pair_left K a b)
      ((K⟮a, b⟯).smul_mem (mem_adjoin_pair_right K a b))

/-- A finite set of generators has a primitive element in its linear span. -/
theorem primitive_in_finset_span (s : Finset L) :
    ∃ a ∈ Submodule.span K (s : Set L), adjoin K (s : Set L) = K⟮a⟯ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp
  | @insert b s hbs ih =>
      obtain ⟨a, ha, hfield⟩ := ih
      obtain ⟨t, ht⟩ := primitive_linear_combination (K := K) b a
      refine ⟨b + t • a, ?_, ?_⟩
      · apply Submodule.add_mem
        · exact Submodule.subset_span (by simp)
        · apply Submodule.smul_mem
          exact Submodule.span_mono (by simp) ha
      · rw [← ht]
        apply le_antisymm
        · rw [adjoin_le_iff]
          intro z hz
          rcases Finset.mem_insert.mp hz with hzb | hz
          · rw [hzb]
            exact mem_adjoin_pair_left K b a
          · have hsub : K⟮a⟯ ≤ K⟮b, a⟯ :=
              adjoin_simple_le_iff.mpr (mem_adjoin_pair_right K b a)
            apply hsub
            rw [← hfield]
            exact subset_adjoin K (s : Set L) hz
        · rw [adjoin_le_iff]
          intro z hz
          rcases Set.mem_insert_iff.mp hz with hzb | hza
          · rw [hzb]
            exact subset_adjoin K (↑(insert b s) : Set L) (by simp)
          · rw [Set.mem_singleton_iff] at hza
            rw [hza]
            have hsub : adjoin K (s : Set L) ≤ adjoin K (↑(insert b s) : Set L) :=
              adjoin.mono K (s : Set L) (↑(insert b s) : Set L) (by simp)
            apply hsub
            rw [hfield]
            exact mem_adjoin_simple_self K a

/-- The primitive element can be taken in the span of any finite generating tuple. -/
theorem primitive_in_coordinate_span {n : ℕ} (p : Vec L n) :
    ∃ a ∈ Submodule.span K (Set.range p), adjoin K (Set.range p) = K⟮a⟯ := by
  classical
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    primitive_in_finset_span (K := K) (Finset.univ.image p)

/-- A specified primitive element yields a power basis indexed by the extension degree. -/
theorem primitive_power_basis {d : ℕ} (hdim : finrank K L = d) (a : L)
    (ha : K⟮a⟯ = ⊤) : ∃ b : Basis (Fin d) K L, ∀ i, b i = a^(i : ℕ) := by
  let p := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := K) a)
  let e := (IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv
  let q := p.map e
  have hgen : q.gen = a := rfl
  have hdimq : q.dim = d := q.finrank.symm.trans hdim
  refine ⟨q.basis.reindex (finCongr hdimq), ?_⟩
  intro i
  rw [Basis.reindex_apply, q.basis_eq_pow, hgen]
  rfl

end
end PfaffianDescent
