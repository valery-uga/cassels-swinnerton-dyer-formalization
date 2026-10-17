import PfaffianDescent.VoisinFourLineCoverage
import PfaffianDescent.TripleQuadricsGlobalThirdRegularity
import AllCharacteristics.ProjectivePoints

/-!
# Four separable lines give regularity without radicality

The finite projective-scheme theorem replaces the earlier use of radicality.
Separable line restrictions supply a nonzero point, so the existing converse
regularity theorem applies to the finite nonempty triple intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite nonempty intersection after a field extension certifies that the
third homogeneous equation is regular over the ground field. -/
theorem cubic_two_quadric_regular_descends_of_finite_nonempty_extension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hfinite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L)))))
    (hnonempty : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L))))) :
    ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map φ) (q.map φ) (r.map φ)
      (hp.map φ) (hq.map φ) (hr.map φ))) := hfinite
  intro F hF
  have hFL : (r.map φ) * F.map φ ∈
      Ideal.span ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    have hm := Ideal.mem_map_of_mem (MvPolynomial.map φ) hF
    simpa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hm
  have hmemL := third_regular_of_finite_degrees
    (p.map φ) (q.map φ) (r.map φ)
    (hp.map φ) (hq.map φ) (hr.map φ) (by decide) (by decide)
    hnonempty (F.map φ) hFL
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  have hmap : I.map (MvPolynomial.map φ) =
      Ideal.span ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    simp [I, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change F ∈ I
  rw [← mvPolynomial_comap_map_coefficientExtension (K := L) I,
    Ideal.mem_comap, hmap]
  exact hmemL

theorem cubic_two_quadric_regular_descends_from_four_separable_lines
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p.map (algebraMap K L))
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (hm : ∀ i, (m i).IsHomogeneous 1)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (u v : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ i j, c.eval (u i j) ≠ 0)
    (hlroots : ∀ i j, (l i).eval (u i j) = 0 ∧
      (l i).eval (v i j) = 0)
    (hmroots : ∀ i j, (m j).eval (u i j) = 0 ∧
      (m j).eval (v i j) = 0)
    (hparam : ∀ i j (y : Fin 4 → L),
      (l i).eval y = 0 → (m j).eval y = 0 →
      ∃ s t : L, y = s • u i j + t • v i j)
    (hsep : ∀ i j,
      (AllCharacteristics.cubicLinePolynomial c (u i j) (v i j)).Separable) :
    ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  let pL := p.map φ
  let qL := q.map φ
  let rL := r.map φ
  let J := tripleCompleteIntersectionHomogeneousIdeal
    pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
  obtain ⟨x, hxinj, hroots, hline⟩ :=
    exists_four_three_point_line_sections_of_separable
      c l m hl hm u v hu hlroots hmroots hparam hsep
  have hline' : ∀ (a b : Fin 2) (y : Fin 4 → L),
      pL.eval y = 0 → (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (t : L), y = t • x a b k := by
    intro a b y hpzero hlzero hmzero
    exact hline a b y (by simpa [pL, hc] using hpzero) hlzero hmzero
  letI : IsFinite (toBase J) :=
    cubic_reducible_two_quadric_intersection_finite_of_four_line_coverage
      pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
      l m hqfactor hrfactor x hline'
  have hroot : ∀ (a b : Fin 2) (k : Fin 3),
      x a b k ∈ MvPolynomial.zeroLocus L J.toIdeal := by
    intro a b k
    apply cubic_reducible_two_quadric_line_roots_mem_zeroLocus
      pL qL rL l m hqfactor hrfactor x
    intro i j z
    simpa [pL, hc] using hroots i j z
  have hxne : x 0 0 0 ≠ 0 ∨ x 0 0 1 ≠ 0 := by
    by_contra h
    push Not at h
    have h01 : x 0 0 0 = x 0 0 1 := h.1.trans h.2.symm
    have hfalse : (0 : Fin 3) = 1 := (hxinj 0 0) h01
    exact Fin.zero_ne_one hfalse
  have hnonempty : Nonempty (scheme J) := by
    rcases hxne with hne | hne
    · obtain ⟨z, -⟩ := point_of_coordinates J (RingHom.id L)
        (x 0 0 0) hne (by
          intro a ha
          exact hroot 0 0 0 a ha)
      exact ⟨z (IsLocalRing.closedPoint L)⟩
    · obtain ⟨z, -⟩ := point_of_coordinates J (RingHom.id L)
        (x 0 0 1) hne (by
          intro a ha
          exact hroot 0 0 1 a ha)
      exact ⟨z (IsLocalRing.closedPoint L)⟩
  exact cubic_two_quadric_regular_descends_of_finite_nonempty_extension
    p q r hp hq hr (by exact inferInstance) hnonempty

end PfaffianDescent
