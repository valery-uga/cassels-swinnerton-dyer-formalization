import PfaffianDescent.QuarticGaloisPairDescent
import PfaffianDescent.QuadraticConjugateDescent

/-! SOURCE ONLY, UNVERIFIED. A genuinely interchanged pair has an internally
constructed quadratic coefficient field. No cubic zero or point-descent
conclusion is used. This applies to matrix entries as well as point vectors. -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- Both exact vectors, not only a projective class, are defined over one
actual degree-two intermediate field. The interchange assumption is derived
from the transitive matching action in an eventual original-line caller. -/
theorem galoisPair_quadratic_coefficient_field
    {J : Type v} (x y : J → K)
    (hpair : ∀ g : K ≃ₐ[k] K,
      ((∀ i, g (x i) = x i) ∧ (∀ i, g (y i) = y i)) ∨
      ((∀ i, g (x i) = y i) ∧ (∀ i, g (y i) = x i)))
    (hnotfixed : ¬ ∀ g : K ≃ₐ[k] K, ∀ i, g (x i) = x i) :
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧ E = IntermediateField.adjoin k (Set.range x) ∧
      ∃ xE yE : J → E, (∀ i, E.val (xE i) = x i) ∧
        (∀ i, E.val (yE i) = y i) := by
  classical
  have hxy : x ≠ y := by
    intro he
    apply hnotfixed
    intro g
    rcases hpair g with h | h
    · exact h.1
    · simpa only [he] using h.1
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  let a := x j
  let a' := y j
  have hd : a - a' ≠ 0 := sub_ne_zero.mpr hj
  have hA (i : J) : ∀ g : K ≃ₐ[k] K,
      g ((a * y i - a' * x i) / (a - a')) =
        (a * y i - a' * x i) / (a - a') := by
    intro g
    rcases hpair g with ⟨hg, hg'⟩ | ⟨hg, hg'⟩
    · simp [a, a', map_div₀, map_sub, map_mul, hg, hg']
    · simp only [map_div₀ g, map_sub g, map_mul g]
      simp only [a, a', hg, hg']
      change (y j * x i - x j * y i) / (y j - x j) =
        (x j * y i - y j * x i) / (x j - y j)
      field_simp [sub_ne_zero.mpr hj, sub_ne_zero.mpr (Ne.symm hj)]
      ring
  have hB (i : J) : ∀ g : K ≃ₐ[k] K,
      g ((x i - y i) / (a - a')) = (x i - y i) / (a - a') := by
    intro g
    rcases hpair g with ⟨hg, hg'⟩ | ⟨hg, hg'⟩
    · simp [a, a', map_div₀, map_sub, hg, hg']
    · simp only [map_div₀ g, map_sub g]
      simp only [a, a', hg, hg']
      change (y i - x i) / (y j - x j) = (x i - y i) / (x j - y j)
      field_simp [sub_ne_zero.mpr hj, sub_ne_zero.mpr (Ne.symm hj)]
      ring
  choose A hAeq using fun i => galois_fixed_element_descends _ (hA i)
  choose B hBeq using fun i => galois_fixed_element_descends _ (hB i)
  have hcoordsX (i : J) :
      algebraMap k K (A i) + algebraMap k K (B i) * a = x i := by
    rw [hAeq, hBeq]
    field_simp [hd]
    ring
  have hcoordsY (i : J) :
      algebraMap k K (A i) + algebraMap k K (B i) * a' = y i := by
    rw [hAeq, hBeq]
    field_simp [hd]
    ring
  have han : a ∉ (algebraMap k K).range := by
    rintro ⟨c, hc⟩
    apply hnotfixed
    intro g i
    rw [← hcoordsX i, map_add, map_mul, AlgEquiv.commutes,
      AlgEquiv.commutes, ← hc, AlgEquiv.commutes]
  obtain ⟨s, hs⟩ := galois_fixed_element_descends (a + a') (by
    intro g
    rcases hpair g with h | h <;>
      simp [a, a', map_add, h.1, h.2, add_comm])
  obtain ⟨t, ht⟩ := galois_fixed_element_descends (a * a') (by
    intro g
    rcases hpair g with h | h <;>
      simp [a, a', map_mul, h.1, h.2, mul_comm])
  let q : Polynomial k := Polynomial.X ^ 2 - Polynomial.C s * Polynomial.X + Polynomial.C t
  have hqmap : q.map (algebraMap k K) =
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C a') := by
    simp [q, hs, ht]
    ring
  have hqdeg : q.natDegree = 2 := by
    rw [← Polynomial.natDegree_map (algebraMap k K), hqmap,
      Polynomial.natDegree_mul (Polynomial.monic_X_sub_C a).ne_zero
        (Polynomial.monic_X_sub_C a').ne_zero]
    simp
  have hqzero : Polynomial.aeval a q = 0 := by
    simp [q, hs, ht]
    ring
  have hai : IsIntegral k a := Algebra.IsIntegral.isIntegral a
  have hdeg : (minpoly k a).natDegree = 2 := by
    apply le_antisymm
    · have hqn : q ≠ 0 := by intro h; simp [h] at hqdeg
      exact (Polynomial.natDegree_le_of_dvd
        (minpoly.dvd k a hqzero) hqn).trans_eq hqdeg
    · exact (minpoly.two_le_natDegree_iff hai).mpr han
  let E := IntermediateField.adjoin k ({a} : Set K)
  letI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional hai
  have hE : finrank k E = 2 := (IntermediateField.adjoin.finrank hai).trans hdeg
  letI : Algebra.IsSeparable k E :=
    Algebra.isSeparable_tower_bot_of_isSeparable k E K
  have hG : IsGalois k E := isGalois_of_finrank_two_of_separable hE
  let aE : E := ⟨a, IntermediateField.subset_adjoin k _ (Set.mem_singleton a)⟩
  let a'E : E := algebraMap k E s - aE
  have ha'E : E.val a'E = a' := by
    change algebraMap k K s - a = a'
    rw [hs]
    ring
  let xE : J → E := fun i => algebraMap k E (A i) + algebraMap k E (B i) * aE
  let yE : J → E := fun i => algebraMap k E (A i) + algebraMap k E (B i) * a'E
  have hxE (i : J) : E.val (xE i) = x i := by
    simpa [xE, aE] using hcoordsX i
  have hyE (i : J) : E.val (yE i) = y i := by
    change algebraMap k K (A i) + algebraMap k K (B i) * E.val a'E = y i
    rw [ha'E]
    exact hcoordsY i
  have hGenerated : E = IntermediateField.adjoin k (Set.range x) := by
    apply le_antisymm
    · change IntermediateField.adjoin k ({a} : Set K) ≤ _
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact IntermediateField.subset_adjoin k _ ⟨j, rfl⟩
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro z ⟨i, rfl⟩
      exact hxE i ▸ (xE i).property
  exact ⟨E, inferInstance, hE, hG, hGenerated, xE, yE, hxE, hyE⟩

end PfaffianDescent
