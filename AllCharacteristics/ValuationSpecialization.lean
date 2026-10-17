import PfaffianDescent.Cubic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Homogeneous coordinate specialization over a valuation ring

This is the coordinate part of Sections 3 and 5 of
`all_characteristics_specialization.tex`. The coefficient ring may have mixed
characteristic. No statement assumes a lift, a section, or a rational point
exists unless that point is the input being specialized.
-/

namespace AllCharacteristics

open PfaffianDescent

section IntegralCoordinates
variable {R ι : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- A nonempty finite list of elements of a valuation ring has a member dividing
all its members. Zeros are allowed. -/
theorem exists_coordinate_dvd_finset (x : ι → R) (s : Finset ι)
    (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, x i ∣ x j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hs.elim (fun _ h => (Finset.notMem_empty _ h).elim)
  | @insert a s ha ih =>
    by_cases he : s.Nonempty
    · obtain ⟨i, hi, hdiv⟩ := ih he
      rcases ValuationRing.dvd_total (x a) (x i) with hai | hia
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_rfl
        · exact hai.trans (hdiv j hj)
      · refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hia
        · exact hdiv j hj
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      subst s
      exact ⟨a, by simp, by simp⟩

/-- Remove a common nonzero scalar from integral homogeneous coordinates so
that one of the resulting coordinates is exactly one. -/
theorem normalize_integral_coordinates [Fintype ι] (x : ι → R) (hx : x ≠ 0) :
    ∃ (a : R) (y : ι → R), a ≠ 0 ∧ x = a • y ∧ ∃ i, y i = 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hs : (Finset.univ : Finset ι).Nonempty := ⟨j, Finset.mem_univ _⟩
  obtain ⟨i, _, hdiv⟩ := exists_coordinate_dvd_finset x Finset.univ hs
  have hi : x i ≠ 0 := by
    intro hi
    have hd := hdiv j (Finset.mem_univ j)
    rw [hi, zero_dvd_iff] at hd
    exact hj hd
  choose y hy using fun j => hdiv j (Finset.mem_univ j)
  refine ⟨x i, y, hi, funext hy, i, ?_⟩
  apply mul_left_cancel₀ hi
  simpa only [mul_one] using (hy i).symm

end IntegralCoordinates

section FractionCoordinates
variable {R K ι : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Fintype ι]

/-- A projective point over the fraction field of a valuation ring admits
integral coordinates with a coordinate equal to one. The equality records that
this is the same projective point, rather than an unrelated special-fiber point. -/
theorem normalize_fraction_coordinates (x : ι → K) (hx : x ≠ 0) :
    ∃ (y : ι → R) (c : K), c ≠ 0 ∧
      (fun i => algebraMap R K (y i)) = c • x ∧ ∃ i, y i = 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) x
  choose z hz using hb
  have hbR : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.property
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hbR
  have hmap : (fun i => algebraMap R K (z i)) = algebraMap R K b • x := by
    funext i
    change algebraMap R K (z i) = algebraMap R K b * x i
    simpa only [Algebra.smul_def] using hz i
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hx
    funext i
    have hi := congrFun hmap i
    simp only [hz0, Pi.zero_apply, map_zero, Pi.smul_apply, smul_eq_mul] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hbK
  obtain ⟨a, y, ha, hzy, hy⟩ := normalize_integral_coordinates z hz0
  have haK : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  refine ⟨y, algebraMap R K b / algebraMap R K a, div_ne_zero hbK haK, ?_, hy⟩
  funext i
  have hi := congrFun hmap i
  simp only [hzy, Pi.smul_apply, smul_eq_mul, map_mul] at hi
  change algebraMap R K (y i) = (algebraMap R K b / algebraMap R K a) * x i
  apply mul_left_cancel₀ haK
  calc
    algebraMap R K a * algebraMap R K (y i) = algebraMap R K b * x i := hi
    _ = algebraMap R K a * ((algebraMap R K b / algebraMap R K a) * x i) := by
      field_simp

end FractionCoordinates

section Cubics
variable {R K k : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [CommRing k] [Nontrivial k] {n : ℕ}

/-- Coordinate specialization of any homogeneous cubic over a valuation ring.
No restriction on either characteristic, smoothness, or the special cubic is
needed. In the addendum, `red` is the residue map of a mixed-characteristic DVR. -/
theorem specialize_cubic (red : R →+* k) (f : Cubic R n)
    (x : Vec K n) (hx : x ≠ 0)
    (hfx : (f.map (algebraMap R K)).eval x = 0) :
    ∃ y : Vec k n, y ≠ 0 ∧ (f.map red).eval y = 0 := by
  obtain ⟨y, c, _, hy, i, hi⟩ := normalize_fraction_coordinates (R := R) x hx
  have hfy : f.eval y = 0 := by
    apply IsFractionRing.injective R K
    rw [map_zero, ← Cubic.eval_map, hy, Cubic.eval_smul, hfx, mul_zero]
  refine ⟨fun j => red (y j), ?_, ?_⟩
  · intro hz
    have hz' := congrFun hz i
    exact one_ne_zero (by simpa only [hi, map_one, Pi.zero_apply] using hz')
  · rw [Cubic.eval_map, hfy, map_zero]

/-- The exact residue-field specialization used for the final rational point. -/
theorem specialize_cubic_to_residue (f : Cubic R n)
    (x : Vec K n) (hx : x ≠ 0)
    (hfx : (f.map (algebraMap R K)).eval x = 0) :
    ∃ y : Vec (IsLocalRing.ResidueField R) n,
      y ≠ 0 ∧ (f.map (IsLocalRing.residue R)).eval y = 0 :=
  specialize_cubic (IsLocalRing.residue R) f x hx hfx

end Cubics
end AllCharacteristics
