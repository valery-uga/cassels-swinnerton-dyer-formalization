import AllCharacteristics.ArbitraryFieldCubicPointDescent
import AllCharacteristics.SchemeQuadraticDescent
import PfaffianDescent.SectionCycles

/-!
# Effective degree-four/five cubic cycles over every field

A cycle of degree four or five has a support point of degree one, two, four,
or five. Quadratic secants and the proved arbitrary-field degree-four/five
point descent give rational sections. Finite closed subschemes are included
through their fundamental cycles, with inseparable degrees and local lengths.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
namespace AllCharacteristics
universe u

/-- A positive weighted sum of degree four or five contains a summand whose
unweighted degree is one, two, four, or five. -/
theorem exists_degree_one_two_four_five_of_sum_four_or_five {ι : Type*}
    (s : Finset ι) (weight degree : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < weight i)
    (h : (∑ i ∈ s, weight i * degree i) = 4 ∨ (∑ i ∈ s, weight i * degree i) = 5) :
    ∃ i ∈ s, degree i = 1 ∨ degree i = 2 ∨ degree i = 4 ∨ degree i = 5 := by
  have hn : ∃ i ∈ s, ¬ 3 ∣ degree i := by
    by_contra hn
    push Not at hn
    have hd : 3 ∣ ∑ i ∈ s, weight i * degree i :=
      Finset.dvd_sum (fun i hi ↦ dvd_mul_of_dvd_right (hn i hi) _)
    omega
  obtain ⟨i, hi, hd⟩ := hn
  have hbound : degree i ≤ 5 := by
    calc
      degree i ≤ weight i * degree i := Nat.le_mul_of_pos_left _ (hw i hi)
      _ ≤ ∑ j ∈ s, weight j * degree j :=
        Finset.single_le_sum (fun j _ ↦ Nat.zero_le (weight j * degree j)) hi
      _ ≤ 5 := by omega
  exact ⟨i, hi, by omega⟩

/-- A degree-eleven effective cycle either has a support point of degree at
most five that already gives a rational point on a cubic surface, or has a
support point of degree eight or eleven. This numerical reduction does not
require the cycle to arise from a reduced finite subscheme. -/
theorem exists_degree_one_two_four_five_eight_eleven_of_sum_eleven {ι : Type*}
    (s : Finset ι) (weight degree : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < weight i)
    (h : (∑ i ∈ s, weight i * degree i) = 11) :
    ∃ i ∈ s, degree i = 1 ∨ degree i = 2 ∨ degree i = 4 ∨
      degree i = 5 ∨ degree i = 8 ∨ degree i = 11 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hnondiv : ∃ i ∈ s, ¬ 3 ∣ degree i := by
    by_contra hn
    push_neg at hn
    have hd : 3 ∣ ∑ i ∈ s, weight i * degree i :=
      Finset.dvd_sum (fun i hi ↦ dvd_mul_of_dvd_right (hn i hi) _)
    omega
  obtain ⟨i, hi, hni⟩ := hnondiv
  have hbound : degree i ≤ 11 := by
    calc
      degree i ≤ weight i * degree i := Nat.le_mul_of_pos_left _ (hw i hi)
      _ ≤ ∑ j ∈ s, weight j * degree j :=
        Finset.single_le_sum (fun j _ ↦ Nat.zero_le (weight j * degree j)) hi
      _ = 11 := h
  have hcases : degree i = 7 ∨ degree i = 10 := by
    have hnot := hnone i hi
    omega
  have hweight : weight i = 1 := by
    have hsingle : weight i * degree i ≤ 11 := by
      calc
        weight i * degree i ≤ ∑ j ∈ s, weight j * degree j :=
          Finset.single_le_sum (fun j _ ↦ Nat.zero_le (weight j * degree j)) hi
        _ = 11 := h
    rcases hcases with hseven | hten
    · rw [hseven] at hsingle
      nlinarith [hw i hi]
    · rw [hten] at hsingle
      nlinarith [hw i hi]
  have hrest : (∑ j ∈ s.erase i, weight j * degree j) = 4 ∨
      (∑ j ∈ s.erase i, weight j * degree j) = 1 := by
    rw [← s.sum_erase_add (fun j ↦ weight j * degree j) hi] at h
    rcases hcases with hseven | hten
    · rw [hseven, hweight] at h
      omega
    · rw [hten, hweight] at h
      omega
  have hsmall : (∑ j ∈ s.erase i, weight j * degree j) = 4 ∨
      (∑ j ∈ s.erase i, weight j * degree j) = 5 := by
    rcases hrest with hfour | hone
    · exact Or.inl hfour
    · have hpos : ∃ j ∈ s.erase i, degree j = 1 := by
        have hsumne : (∑ j ∈ s.erase i, weight j * degree j) ≠ 0 := by omega
        obtain ⟨j, hj, hjnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
        refine ⟨j, hj, ?_⟩
        have hjbound : weight j * degree j ≤ 1 := by
          calc
            weight j * degree j ≤ ∑ t ∈ s.erase i, weight t * degree t :=
              Finset.single_le_sum (fun t _ ↦ Nat.zero_le (weight t * degree t)) hj
            _ = 1 := hone
        have hjpos : 0 < weight j := hw j (Finset.mem_of_mem_erase hj)
        have hprod : weight j * degree j = 1 := by omega
        nlinarith
      obtain ⟨j, hj, hd⟩ := hpos
      exact False.elim ((hnone j (Finset.mem_of_mem_erase hj)).1 hd)
  obtain ⟨j, hj, hd⟩ := exists_degree_one_two_four_five_of_sum_four_or_five
    (s.erase i) weight degree
    (fun j hj ↦ hw j (Finset.mem_of_mem_erase hj)) hsmall
  have hnot := hnone j (Finset.mem_of_mem_erase hj)
  rcases hd with h1 | h2 | h4 | h5
  · exact hnot.1 h1
  · exact hnot.2.1 h2
  · exact hnot.2.2.1 h4
  · exact hnot.2.2.2.1 h5

/-- The degree-eight analogue: unless a support point has one of the small
degrees that gives a rational point on a cubic, the cycle has a degree-eight
support point. -/
theorem exists_degree_one_two_four_five_eight_of_sum_eight {ι : Type*}
    (s : Finset ι) (weight degree : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < weight i)
    (h : (∑ i ∈ s, weight i * degree i) = 8) :
    ∃ i ∈ s, degree i = 1 ∨ degree i = 2 ∨ degree i = 4 ∨
      degree i = 5 ∨ degree i = 8 := by
  classical
  by_contra hnone
  push Not at hnone
  have hnondiv : ∃ i ∈ s, ¬ 3 ∣ degree i := by
    by_contra hn
    push Not at hn
    have hd : 3 ∣ ∑ i ∈ s, weight i * degree i :=
      Finset.dvd_sum (fun i hi ↦ dvd_mul_of_dvd_right (hn i hi) _)
    omega
  obtain ⟨i, hi, hni⟩ := hnondiv
  have hbound : degree i ≤ 8 := by
    calc
      degree i ≤ weight i * degree i := Nat.le_mul_of_pos_left _ (hw i hi)
      _ ≤ ∑ j ∈ s, weight j * degree j :=
        Finset.single_le_sum (fun j _ ↦ Nat.zero_le (weight j * degree j)) hi
      _ = 8 := h
  have hseven : degree i = 7 := by
    have hnot := hnone i hi
    omega
  have hsingle : weight i * degree i ≤ 8 := by
    calc
      weight i * degree i ≤ ∑ j ∈ s, weight j * degree j :=
        Finset.single_le_sum (fun j _ ↦ Nat.zero_le (weight j * degree j)) hi
      _ = 8 := h
  have hweight : weight i = 1 := by
    rw [hseven] at hsingle
    nlinarith [hw i hi]
  have hrest : (∑ j ∈ s.erase i, weight j * degree j) = 1 := by
    rw [← s.sum_erase_add (fun j ↦ weight j * degree j) hi] at h
    rw [hseven, hweight] at h
    omega
  have hsumne : (∑ j ∈ s.erase i, weight j * degree j) ≠ 0 := by omega
  obtain ⟨j, hj, hjnonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hjbound : weight j * degree j ≤ 1 := by
    calc
      weight j * degree j ≤ ∑ t ∈ s.erase i, weight t * degree t :=
        Finset.single_le_sum (fun t _ ↦ Nat.zero_le (weight t * degree t)) hj
      _ = 1 := hrest
  have hjpos : 0 < weight j := hw j (Finset.mem_of_mem_erase hj)
  have hprod : weight j * degree j = 1 := by omega
  have hdeg : degree j = 1 := by nlinarith
  exact (hnone j (Finset.mem_of_mem_erase hj)).1 hdeg

/-- An effective cycle of degree four or five has a closed support point of
degree one, two, four, or five. -/
theorem EffectiveZeroCycle.exists_degree_one_two_four_five
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (hz : EffectiveZeroCycle.degree f z = 4 ∨ EffectiveZeroCycle.degree f z = 5) :
    ∃ x ∈ z.support,
      f.residueDegree x.1 = 1 ∨ f.residueDegree x.1 = 2 ∨
      f.residueDegree x.1 = 4 ∨ f.residueDegree x.1 = 5 :=
  exists_degree_one_two_four_five_of_sum_four_or_five z.support z
    (fun x ↦ f.residueDegree x.1)
    (fun _x hx ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)) hz

/-- The support-degree alternative for an arbitrary effective cycle of
degree eleven, with multiplicities included. -/
theorem EffectiveZeroCycle.exists_degree_one_two_four_five_eight_eleven
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (hz : EffectiveZeroCycle.degree f z = 11) :
    ∃ x ∈ z.support,
      f.residueDegree x.1 = 1 ∨ f.residueDegree x.1 = 2 ∨
      f.residueDegree x.1 = 4 ∨ f.residueDegree x.1 = 5 ∨
      f.residueDegree x.1 = 8 ∨ f.residueDegree x.1 = 11 :=
  exists_degree_one_two_four_five_eight_eleven_of_sum_eleven z.support z
    (fun x ↦ f.residueDegree x.1)
    (fun _x hx ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)) hz

/-- The corresponding support-degree alternative for a degree-eight cycle. -/
theorem EffectiveZeroCycle.exists_degree_one_two_four_five_eight
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (hz : EffectiveZeroCycle.degree f z = 8) :
    ∃ x ∈ z.support,
      f.residueDegree x.1 = 1 ∨ f.residueDegree x.1 = 2 ∨
      f.residueDegree x.1 = 4 ∨ f.residueDegree x.1 = 5 ∨
      f.residueDegree x.1 = 8 :=
  exists_degree_one_two_four_five_eight_of_sum_eight z.support z
    (fun x ↦ f.residueDegree x.1)
    (fun _x hx ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)) hz

open HomogeneousProjective

/-- Every effective cycle of degree four or five on a nonzero smooth cubic
surface gives a rational section over its original field, in every characteristic. -/
theorem cubic_section_of_effective_degree_four_or_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, _, hx⟩ := EffectiveZeroCycle.exists_degree_one_two_four_five
    (hypersurfaceToBase p hp) z hz
  rcases hx with h1 | h2 | h4 | h5
  · exact hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega)
  · exact hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega)
  · exact cubic_section_of_closedPoint_degree_four_or_five p hp hne x (Or.inl h4)
  · exact cubic_section_of_closedPoint_degree_four_or_five p hp hne x (Or.inr h5)

/-- An effective degree-eleven cycle either already gives a rational point,
or supplies a closed point of degree eight or eleven. This is the
cycle-to-closed-point reduction needed before applying Voisin's later generic
configuration constructions. -/
theorem cubic_section_or_closedPoint_degree_eight_or_eleven_of_effective_degree_eleven
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11) :
    (∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 8 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 11) := by
  obtain ⟨x, _, hdeg⟩ := EffectiveZeroCycle.exists_degree_one_two_four_five_eight_eleven
    (hypersurfaceToBase p hp) z hz
  rcases hdeg with h1 | h2 | h4 | h5 | h8 | h11
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inl (cubic_section_of_closedPoint_degree_four_or_five
      p hp hne x (Or.inl h4))
  · exact Or.inl (cubic_section_of_closedPoint_degree_four_or_five
      p hp hne x (Or.inr h5))
  · exact Or.inr ⟨x, Or.inl h8⟩
  · exact Or.inr ⟨x, Or.inr h11⟩

/-- A degree-eight effective cycle on a smooth cubic either yields a rational
point or contains a degree-eight closed point. -/
theorem cubic_section_or_closedPoint_degree_eight_of_effective_degree_eight
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8) :
    (∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 8) := by
  obtain ⟨x, _, hdeg⟩ := EffectiveZeroCycle.exists_degree_one_two_four_five_eight
    (hypersurfaceToBase p hp) z hz
  rcases hdeg with h1 | h2 | h4 | h5 | h8
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inl (cubic_section_of_closedPoint_degree_four_or_five
      p hp hne x (Or.inl h4))
  · exact Or.inl (cubic_section_of_closedPoint_degree_four_or_five
      p hp hne x (Or.inr h5))
  · exact Or.inr ⟨x, h8⟩

/-- The arbitrary-field effective-cycle theorem also gives rational coordinates. -/
theorem cubic_coordinates_of_effective_degree_four_or_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨a, ha⟩ := cubic_section_of_effective_degree_four_or_five p hp hne z hz
  exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)

/-- Effective cycles of degrees four and five are equivalent on a nonzero
smooth cubic surface over every field.  Each direction uses the rational
section supplied by the arbitrary-field degree-four/five descent and then
the standard section cycle of the opposite degree. -/
theorem cubic_effective_degree_four_iff_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ↔
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs⟩ := cubic_section_of_effective_degree_four_or_five
      p hp hne z (Or.inl hz)
    exact PfaffianDescent.effective_cycle_of_section
      (hypersurfaceToBase p hp) s hs 5
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs⟩ := cubic_section_of_effective_degree_four_or_five
      p hp hne z (Or.inr hz)
    exact PfaffianDescent.effective_cycle_of_section
      (hypersurfaceToBase p hp) s hs 4

/-- A finite closed subscheme of rank four or five on a nonzero smooth cubic
surface produces a rational section over every field, including nonreduced
subschemes and inseparable residue points. -/
theorem cubic_section_of_finite_closed_subscheme_rank_four_or_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 4 ∨
      finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i (hypersurfaceToBase p hp)
  apply cubic_section_of_effective_degree_four_or_five p hp hne z
  rwa [hz]

end AllCharacteristics
