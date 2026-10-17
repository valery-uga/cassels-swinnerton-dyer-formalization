import PfaffianDescent.VoisinQuadraticSpanDescent
import PfaffianDescent.VoisinTwelvePointEvaluationFaithful
import PfaffianDescent.PolynomialIdealDescent

/-!
# Descending detection from a split twelve-point intersection

The twelve geometric points may be defined only after a field extension.
Nullstellensatz detects the quadratic equations over the algebraically closed
extension; faithful flatness descends the resulting two-quadric linear span
back to the ground field.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Detection by twelve geometric projective points descends in every
positive homogeneous degree, not just degree two. The points and the
radicality certificate may live over an algebraically closed extension. -/
theorem homogeneous_detection_descends_from_split_twelve_points
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r t : MvPolynomial (Fin 4) K)
    (d : ℕ) (hd : 0 < d) (ht : t.IsHomogeneous d)
    (IL : Ideal (MvPolynomial (Fin 4) L))
    (hIL : IL = Ideal.span ({p.map (algebraMap K L),
      q.map (algebraMap K L), r.map (algebraMap K L)} :
        Set (MvPolynomial (Fin 4) L)))
    (hrad : IL.IsRadical)
    (x : Fin 12 → Fin 4 → L)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus L IL,
      y = 0 ∨ ∃ (i : Fin 12) (c : L), y = c • x i)
    (hzero : ∀ i, MvPolynomial.aeval (x i)
      (t.map (algebraMap K L)) = 0) :
    t ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) := by
  let Q : Fin 3 → MvPolynomial (Fin 4) K := ![p, q, r]
  have hrange : Set.range Q = ({p, q, r} : Set (MvPolynomial (Fin 4) K)) := by
    ext s
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp [Q]⟩
      · exact ⟨1, by simp [Q]⟩
      · exact ⟨2, by simp [Q]⟩
  have hrangeL : Set.range (fun i : Fin 3 =>
      (Q i).map (algebraMap K L)) =
      ({p.map (algebraMap K L), q.map (algebraMap K L),
        r.map (algebraMap K L)} : Set (MvPolynomial (Fin 4) L)) := by
    ext s
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp [Q]⟩
      · exact ⟨1, by simp [Q]⟩
      · exact ⟨2, by simp [Q]⟩
  have hmemL : t.map (algebraMap K L) ∈ IL :=
    homogeneous_mem_ideal_of_twelve_projective_evaluations_zero
      IL hrad x hcover d hd _ (ht.map (algebraMap K L)) hzero
  have hdesc : t ∈ Ideal.span (Set.range Q) := by
    apply polynomial_mem_span_map_range_descends (k := K) (K := L) Q t
    rw [hrangeL, ← hIL]
    exact hmemL
  rwa [hrange] at hdesc

/-- If the extended cubic--quadric--quadric ideal is radical and its affine
cone is covered by twelve geometric lines, quadratic detection descends to
the ground field. The twelve points need not be ground-field rational. -/
theorem quadratic_detection_descends_from_split_twelve_points
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r t : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (ht : t.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (IL : Ideal (MvPolynomial (Fin 4) L))
    (hIL : IL = Ideal.span ({p.map (algebraMap K L),
      q.map (algebraMap K L), r.map (algebraMap K L)} :
        Set (MvPolynomial (Fin 4) L)))
    (hrad : IL.IsRadical)
    (x : Fin 12 → Fin 4 → L)
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus L IL,
      y = 0 ∨ ∃ (i : Fin 12) (c : L), y = c • x i)
    (hzero : ∀ i, MvPolynomial.aeval (x i)
      (t.map (algebraMap K L)) = 0) :
    t ∈ I := by
  obtain ⟨a, b, hab⟩ :=
    quadratic_vanishing_at_twelve_eq_defining_quadric_span
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L)) (t.map (algebraMap K L))
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L)) (ht.map (algebraMap K L))
      IL hIL hrad x hcover hzero
  obtain ⟨c, d, hcd⟩ := polynomial_pair_span_descends q r t ⟨a, b, hab⟩
  rw [hI]
  exact (quadratic_mem_cubic_two_quadric_ideal_iff_scalar_span
    p q r t hp hq hr ht).mpr ⟨c, d, hcd⟩

end PfaffianDescent
