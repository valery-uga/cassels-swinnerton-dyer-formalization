import PfaffianDescent.TripleCompleteIntersectionLength
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Sequential regularity for three quadrics

This identifies the explicit non-zero-divisor conditions used by the concrete
Koszul calculations with Mathlib's standard regular-sequence predicate.
-/

namespace PfaffianDescent

open MvPolynomial
open RingTheory.Sequence

section

variable {K : Type*} [Field K]

private lemma ofList_singleton_smul_top_eq_span
    (f : MvPolynomial (Fin 4) K) :
    (Ideal.ofList [f] • (⊤ : Submodule (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K))) =
      Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) := by
  rw [Ideal.ofList_singleton]
  simpa using (Ideal.smul_top_eq_map (S := MvPolynomial (Fin 4) K)
    (Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))))

private lemma ofList_pair_smul_top_eq_span
    (f g : MvPolynomial (Fin 4) K) :
    (Ideal.ofList [f, g] • (⊤ : Submodule (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K))) =
      Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) := by
  have heq : Ideal.ofList [f, g] =
      Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) := by
    apply congrArg Ideal.span
    ext r
    simp
  rw [heq]
  simpa using (Ideal.smul_top_eq_map (S := MvPolynomial (Fin 4) K)
    (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))))

private lemma one_not_mem_span_pair_homogeneous_quadrics
    (f g : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) :
    (1 : MvPolynomial (Fin 4) K) ∉
      Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) := by
  intro hmem
  have hker : Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 4) K →+* K) := by
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.coeff 0 q = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq
    · simpa [hq] using hf.coeff_eq_zero (by norm_num)
    · simpa [hq] using hg.coeff_eq_zero (by norm_num)
  have hzero := hker hmem
  change MvPolynomial.constantCoeff (1 : MvPolynomial (Fin 4) K) = 0 at hzero
  have hzero' : (1 : K) = 0 := by simpa using hzero
  exact one_ne_zero hzero'

/-- The explicit sequential non-zero-divisor conditions imply the weak
regularity of the ordered three-quadric sequence. -/
theorem triple_quadrics_isWeaklyRegular_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K) (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsWeaklyRegular (MvPolynomial (Fin 4) K) [f, g, h] := by
  rw [isWeaklyRegular_iff_Fin]
  intro i
  fin_cases i
  · rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro p hp
    have hp0 : f * p = 0 := by
      simpa [Ideal.ofList_nil] using hp
    have hpzero : p = 0 := (mul_eq_zero.mp hp0).resolve_left hf0
    simpa [Ideal.ofList_nil] using hpzero
  · simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add]
    let e := Submodule.quotEquivOfEq _ _
      (ofList_singleton_smul_top_eq_span (K := K) f)
    exact (e.isSMulRegular_congr g).mpr
      ((isSMulRegular_quotient_iff_mem_of_smul_mem
        (Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))) g).mpr hgreg)
  · simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add]
    let e := Submodule.quotEquivOfEq _ _
      (ofList_pair_smul_top_eq_span (K := K) f g)
    exact (e.isSMulRegular_congr h).mpr
      ((isSMulRegular_quotient_iff_mem_of_smul_mem
        (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) h).mpr hhregular)

/-- Weak regularity of the ordered three-quadric sequence recovers each
explicit non-zero-divisor condition used by the Koszul calculations. -/
theorem triple_quadrics_sequential_regular_of_isWeaklyRegular
    (f g h : MvPolynomial (Fin 4) K)
    (hseq : IsWeaklyRegular (MvPolynomial (Fin 4) K) [f, g, h]) :
    f ≠ 0 ∧
      (∀ x : MvPolynomial (Fin 4) K,
        g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
          x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))) ∧
      (∀ x : MvPolynomial (Fin 4) K,
        h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
          x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) := by
  have h0 := hseq.regular_mod_prev 0 (by simp)
  have hf0 : f ≠ 0 := by
    intro hf
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at h0
    have h1 := h0 1 (by simp [hf])
    simpa [Ideal.ofList_nil] using h1
  refine ⟨hf0, ?_, ?_⟩
  · have h1 := hseq.regular_mod_prev 1 (by simp)
    simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add] at h1
    let e := Submodule.quotEquivOfEq _ _
      (ofList_singleton_smul_top_eq_span (K := K) f)
    have h1' : IsSMulRegular
        (MvPolynomial (Fin 4) K ⧸
          Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))) g :=
      (e.isSMulRegular_congr g).mp h1
    exact (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))) g).mp h1'
  · have h2 := hseq.regular_mod_prev 2 (by simp)
    simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add] at h2
    let e := Submodule.quotEquivOfEq _ _
      (ofList_pair_smul_top_eq_span (K := K) f g)
    have h2' : IsSMulRegular
        (MvPolynomial (Fin 4) K ⧸
          Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) h :=
      (e.isSMulRegular_congr h).mp h2
    exact (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) h).mp h2'

/-- The three generators of a sequentially regular net of homogeneous
quadrics are linearly independent.  This supplies the degree-two dimension
assertion in the accompanying remark of `lem:net-of-quadrics`. -/
theorem triple_quadrics_linearIndependent_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    LinearIndependent K ![f, g, h] := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum i
  rw [Fin.sum_univ_three] at hsum
  have hsum' : a 0 • f + a 1 • g + a 2 • h = 0 := by simpa using hsum
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))
  have hnotone : (1 : MvPolynomial (Fin 4) K) ∉ I :=
    one_not_mem_span_pair_homogeneous_quadrics f g hf hg
  have hfI : f ∈ I := Ideal.subset_span (by simp)
  have hgI : g ∈ I := Ideal.subset_span (by simp)
  have hsumI : a 0 • f + a 1 • g ∈ I := by
    apply I.add_mem
    · rw [smul_eq_C_mul]
      exact I.mul_mem_left _ hfI
    · rw [smul_eq_C_mul]
      exact I.mul_mem_left _ hgI
  by_cases ha2 : a 2 = 0
  · have hsum'' : a 0 • f + a 1 • g = 0 := by simpa [ha2] using hsum'
    by_cases ha1 : a 1 = 0
    · have hsum''' : a 0 • f = 0 := by simpa [ha1] using hsum''
      have ha0 : a 0 = 0 := (smul_eq_zero.mp hsum''').resolve_right hf0
      fin_cases i <;> simp [ha0, ha1, ha2]
    · exfalso
      let J : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))
      have hfJ : f ∈ J := Ideal.subset_span (by simp)
      have hlin : a 1 • g ∈ J := by
        rw [eq_neg_of_add_eq_zero_right hsum'']
        rw [smul_eq_C_mul]
        exact J.neg_mem (J.mul_mem_left _ hfJ)
      have hgJ : g ∈ J := by
        have heq : g = (a 1)⁻¹ • (a 1 • g) := by
          calc
            g = 1 • g := (one_smul K g).symm
            _ = ((a 1)⁻¹ * a 1) • g := by rw [inv_mul_cancel₀ ha1]
            _ = (a 1)⁻¹ • (a 1 • g) := (smul_smul _ _ _).symm
        rw [heq, smul_eq_C_mul]
        exact J.mul_mem_left _ hlin
      have honeJ : (1 : MvPolynomial (Fin 4) K) ∈ J := hgreg 1 (by simpa using hgJ)
      apply hnotone
      exact Ideal.span_mono (by simp) honeJ
  · exfalso
    have hlin : a 2 • h ∈ I := by
      rw [eq_neg_of_add_eq_zero_right hsum']
      exact I.neg_mem hsumI
    have hhI : h ∈ I := by
      have heq : h = (a 2)⁻¹ • (a 2 • h) := by
        calc
          h = 1 • h := (one_smul K h).symm
          _ = ((a 2)⁻¹ * a 2) • h := by rw [inv_mul_cancel₀ ha2]
          _ = (a 2)⁻¹ • (a 2 • h) := (smul_smul _ _ _).symm
      rw [heq, smul_eq_C_mul]
      exact I.mul_mem_left _ hlin
    apply hnotone
    exact hhregular 1 (by simpa using hhI)

/-- Standard regularity of three homogeneous quadrics also makes their
generators linearly independent. -/
theorem triple_quadrics_linearIndependent_of_isRegular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hseq : IsRegular (MvPolynomial (Fin 4) K) [f, g, h]) :
    LinearIndependent K ![f, g, h] := by
  obtain ⟨hf0, hgreg, hhregular⟩ :=
    triple_quadrics_sequential_regular_of_isWeaklyRegular f g h hseq.toIsWeaklyRegular
  exact triple_quadrics_linearIndependent_of_sequential_regular
    f g h hf hg hf0 hgreg hhregular

/-- Positive-degree homogeneous quadrics satisfying the explicit sequential
conditions form a regular sequence in the standard sense. -/
theorem triple_quadrics_isRegular_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsRegular (MvPolynomial (Fin 4) K) [f, g, h] := by
  refine ⟨triple_quadrics_isWeaklyRegular_of_sequential_regular
    f g h hf0 hgreg hhregular, ?_⟩
  intro htop
  have hI : Ideal.ofList [f, g, h] ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 4) K →+* K) := by
    apply Ideal.span_le.mpr
    intro x hx
    have hfcoeff : MvPolynomial.coeff 0 f = 0 := hf.coeff_eq_zero (by norm_num)
    have hgcoeff : MvPolynomial.coeff 0 g = 0 := hg.coeff_eq_zero (by norm_num)
    have hhcoeff : MvPolynomial.coeff 0 h = 0 := hh.coeff_eq_zero (by norm_num)
    change x ∈ [f, g, h] at hx
    change MvPolynomial.coeff 0 x = 0
    rcases List.mem_cons.mp hx with hxf | hx
    · simpa [hxf] using hfcoeff
    rcases List.mem_cons.mp hx with hxg | hx
    · simpa [hxg] using hgcoeff
    rw [List.mem_singleton] at hx
    simpa [hx] using hhcoeff
  have h1 : (1 : MvPolynomial (Fin 4) K) ∈
      Ideal.ofList [f, g, h] • (⊤ : Submodule (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K)) := by
    rw [← htop]
    exact Submodule.mem_top
  have heq : Ideal.ofList [f, g, h] •
      (⊤ : Submodule (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) =
      Ideal.ofList [f, g, h] := by
    simpa using (Ideal.smul_top_eq_map (S := MvPolynomial (Fin 4) K)
      (Ideal.ofList [f, g, h]))
  rw [heq] at h1
  have hone := hI h1
  change MvPolynomial.constantCoeff (1 : MvPolynomial (Fin 4) K) = 0 at hone
  have hone' : (1 : K) = 0 := by simpa using hone
  exact one_ne_zero hone'

/-- The sequential non-zero-divisor conditions for three homogeneous cubics
give a regular sequence. The weak-regularity argument is independent of the
degrees; positive degree makes the generated ideal proper. -/
theorem triple_cubics_isRegular_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hh : h.IsHomogeneous 3)
    (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsRegular (MvPolynomial (Fin 4) K) [f, g, h] := by
  refine ⟨triple_quadrics_isWeaklyRegular_of_sequential_regular
    f g h hf0 hgreg hhregular, ?_⟩
  intro htop
  have hI : Ideal.ofList [f, g, h] ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 4) K →+* K) := by
    apply Ideal.span_le.mpr
    intro x hx
    have hfcoeff : MvPolynomial.coeff 0 f = 0 := hf.coeff_eq_zero (by norm_num)
    have hgcoeff : MvPolynomial.coeff 0 g = 0 := hg.coeff_eq_zero (by norm_num)
    have hhcoeff : MvPolynomial.coeff 0 h = 0 := hh.coeff_eq_zero (by norm_num)
    change x ∈ [f, g, h] at hx
    change MvPolynomial.coeff 0 x = 0
    rcases List.mem_cons.mp hx with hxf | hx
    · simpa [hxf] using hfcoeff
    rcases List.mem_cons.mp hx with hxg | hx
    · simpa [hxg] using hgcoeff
    rw [List.mem_singleton] at hx
    simpa [hx] using hhcoeff
  have h1 : (1 : MvPolynomial (Fin 4) K) ∈
      Ideal.ofList [f, g, h] • (⊤ : Submodule (MvPolynomial (Fin 4) K)
        (MvPolynomial (Fin 4) K)) := by
    rw [← htop]
    exact Submodule.mem_top
  have heq : Ideal.ofList [f, g, h] •
      (⊤ : Submodule (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K)) =
      Ideal.ofList [f, g, h] := by
    simpa using (Ideal.smul_top_eq_map (S := MvPolynomial (Fin 4) K)
      (Ideal.ofList [f, g, h]))
  rw [heq] at h1
  have hone := hI h1
  change MvPolynomial.constantCoeff (1 : MvPolynomial (Fin 4) K) = 0 at hone
  have hone' : (1 : K) = 0 := by simpa using hone
  exact one_ne_zero hone'

/-- For homogeneous quadrics, the standard regular-sequence predicate is
equivalent to the explicit conditions used by the three-generator Koszul
development. -/
theorem triple_quadrics_isRegular_iff_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2) :
    IsRegular (MvPolynomial (Fin 4) K) [f, g, h] ↔
      f ≠ 0 ∧
        (∀ x : MvPolynomial (Fin 4) K,
          g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
            x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K))) ∧
        (∀ x : MvPolynomial (Fin 4) K,
          h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
            x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) := by
  constructor
  · intro hseq
    exact triple_quadrics_sequential_regular_of_isWeaklyRegular
      f g h hseq.toIsWeaklyRegular
  · rintro ⟨hf0, hgreg, hhregular⟩
    exact triple_quadrics_isRegular_of_sequential_regular
      f g h hf hg hh hf0 hgreg hhregular

end

end PfaffianDescent
