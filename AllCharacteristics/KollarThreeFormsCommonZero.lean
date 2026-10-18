import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-! The height argument used for two forms extends to three forms in four variables.
This is the geometric ingredient in Kollár, §18; no perfectness is needed. -/

namespace PfaffianDescent
open MvPolynomial
universe u

theorem height_idealOfVars_le_three_of_radical_eq_span_triple
    {K : Type u} [Field K] (a b c : MvPolynomial (Fin 4) K)
    (hrad : (Ideal.span ({a, b, c} : Set (MvPolynomial (Fin 4) K))).radical =
      MvPolynomial.idealOfVars (Fin 4) K) :
    (MvPolynomial.idealOfVars (Fin 4) K).height ≤ 3 := by
  have hminimal := idealOfVars_mem_minimalPrimes_of_radical_eq
    (Ideal.span ({a, b, c} : Set (MvPolynomial (Fin 4) K))) hrad
  have hbound := Ideal.height_le_card_of_mem_minimalPrimes_span
    (p := MvPolynomial.idealOfVars (Fin 4) K)
    (s := ({a, b, c} : Set (MvPolynomial (Fin 4) K))) (by simp) hminimal
  apply hbound.trans
  exact_mod_cast
    (calc
      ({a, b, c} : Set (MvPolynomial (Fin 4) K)).ncard ≤
          ({b, c} : Set _).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ (({c} : Set _).ncard + 1) + 1 :=
        Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
      _ = 3 := by simp)

/-- Three positive-degree forms in four variables have a nonzero common
geometric zero. The statement includes identically zero forms. -/
theorem exists_nonzero_common_zero_three_of_homogeneous_pos
    {K : Type u} [Field K] [IsAlgClosed K]
    (a b c : MvPolynomial (Fin 4) K) {m n r : ℕ}
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous n) (hc : c.IsHomogeneous r)
    (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧
      MvPolynomial.aeval x a = 0 ∧ MvPolynomial.aeval x b = 0 ∧
      MvPolynomial.aeval x c = 0 := by
  classical
  by_contra h
  have ha0 := aeval_zero_eq_zero_of_homogeneous_pos a ha hm
  have hb0 := aeval_zero_eq_zero_of_homogeneous_pos b hb hn
  have hc0 := aeval_zero_eq_zero_of_homogeneous_pos c hc hr
  let I := Ideal.span ({a, b, c} : Set (MvPolynomial (Fin 4) K))
  have hzero : (0 : Fin 4 → K) ∈ MvPolynomial.zeroLocus K I := by
    rw [MvPolynomial.mem_zeroLocus_iff]
    let f : MvPolynomial (Fin 4) K →+* K :=
      (MvPolynomial.aeval (0 : Fin 4 → K)).toRingHom
    have hspan : I ≤ RingHom.ker f := by
      apply Ideal.span_le.2
      rintro z (rfl | rfl | rfl)
      · exact ha0
      · exact hb0
      · exact hc0
    intro p hp
    exact hspan hp
  have honly : MvPolynomial.zeroLocus K I ≤ ({0} : Set (Fin 4 → K)) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hx0
    have hvan := MvPolynomial.mem_zeroLocus_iff.mp hx
    have hax : MvPolynomial.aeval x a = 0 :=
      hvan a (Ideal.subset_span (by simp))
    have hbx : MvPolynomial.aeval x b = 0 :=
      hvan b (Ideal.subset_span (by simp))
    have hcx : MvPolynomial.aeval x c = 0 :=
      hvan c (Ideal.subset_span (by simp))
    exact h ⟨x, hx0, hax, hbx, hcx⟩
  have hrad := radical_eq_idealOfVars_of_zeroLocus_subset_origin I hzero honly
  have hle := height_idealOfVars_le_three_of_radical_eq_span_triple a b c hrad
  have hbad : (4 : ℕ∞) ≤ 3 := (four_le_height_idealOfVars (K := K)).trans hle
  norm_num at hbad

end PfaffianDescent
