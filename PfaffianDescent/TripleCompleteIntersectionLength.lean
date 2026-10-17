import PfaffianDescent.TripleCompleteIntersectionHilbert
import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import PfaffianDescent.ProjectiveLengthOfHilbert
import PfaffianDescent.VoisinRegularSequenceCriteria

/-!
# Lengths of the complete intersections in Voisin's residual steps
-/

namespace PfaffianDescent

open AlgebraicGeometry Module
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K : Type u} [Field K] [Infinite K]

omit [Infinite K] in
/-- Three cubics satisfying the explicit regularity hypotheses define an
actual finite projective scheme. -/
theorem triple_cubic_intersection_finite
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
  apply projective_finite_of_hilbert_bound
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 9 27
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) ≤ 27
  have hdim := triple_cubic_hilbert_twenty_seven
    f g h hf hg hh hf0 hg0 hrel hregular (n - 9)
  rw [Nat.sub_add_cancel hn] at hdim
  exact hdim.le

/-- The projective intersection of three regular cubics has scheme-theoretic
length 27. -/
theorem triple_cubic_intersection_length_twenty_seven
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    letI := triple_cubic_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 27 := by
  let _ := triple_cubic_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  apply projective_length_of_eventual_hilbert
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 9 27
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) = 27
  have hdim := triple_cubic_hilbert_twenty_seven
    f g h hf hg hh hf0 hg0 hrel hregular (n - 9)
  rwa [Nat.sub_add_cancel hn] at hdim

omit [Infinite K] in
/-- A cubic and two quadrics satisfying the explicit regularity hypotheses
define an actual finite projective scheme. -/
theorem cubic_two_quadrics_intersection_finite
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
  apply projective_finite_of_hilbert_bound
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 7 12
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) ≤ 12
  have hdim := cubic_two_quadrics_hilbert_twelve
    f g h hf hg hh hf0 hg0 hrel hregular (n - 7)
  rw [Nat.sub_add_cancel hn] at hdim
  exact hdim.le

/-- The projective intersection of a cubic and two regular quadrics has
scheme-theoretic length 12. -/
theorem cubic_two_quadrics_intersection_length_twelve
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    letI := cubic_two_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 12 := by
  let _ := cubic_two_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  apply projective_length_of_eventual_hilbert
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 7 12
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) = 12
  have hdim := cubic_two_quadrics_hilbert_twelve
    f g h hf hg hh hf0 hg0 hrel hregular (n - 7)
  rwa [Nat.sub_add_cancel hn] at hdim

omit [Infinite K] in
/-- Three quadrics satisfying the explicit regularity hypotheses define an
actual finite projective scheme. -/
theorem triple_quadrics_intersection_finite
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
  apply projective_finite_of_hilbert_bound
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 6 8
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) ≤ 8
  have hdim := triple_quadrics_hilbert_eight
    f g h hf hg hh hf0 hg0 hrel hregular (n - 6)
  rw [Nat.sub_add_cancel hn] at hdim
  exact hdim.le

omit [Infinite K] in
/-- The finite form of the three-quadric Bézout calculation under the
usual sequential regularity hypotheses.  The second equation is regular
modulo the first, and the third is regular modulo the first two. -/
theorem triple_quadrics_intersection_finite_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) := by
  apply triple_quadrics_intersection_finite f g h hf hg hh hf0
  · exact right_ne_zero_of_regular_mod_span_singleton
      (homogeneous_not_isUnit_of_pos_degree hf (by omega)) hgreg
  · exact isRelPrime_of_regular_mod_span_singleton hf0 hgreg
  · exact hhregular

/-- The projective intersection of three regular quadrics has
scheme-theoretic length eight. This is the Bézout step in the
net-of-quadrics argument of Section 4. -/
theorem triple_quadrics_intersection_length_eight
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    letI := triple_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 := by
  let _ := triple_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  apply projective_length_of_eventual_hilbert
    (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh) 6 8
  intro n hn
  change finrank K (tripleCompleteIntersectionComponent f g h n) = 8
  have hdim := triple_quadrics_hilbert_eight
    f g h hf hg hh hf0 hg0 hrel hregular (n - 6)
  rwa [Nat.sub_add_cancel hn] at hdim

/-- The rank-eight Bézout conclusion under the ordinary sequential
regularity hypotheses for the three quadrics. -/
theorem triple_quadrics_intersection_length_eight_of_sequential_regular
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0)
    (hgreg : ∀ x : MvPolynomial (Fin 4) K,
      g * x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f} : Set (MvPolynomial (Fin 4) K)))
    (hhregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))) :
    letI := triple_quadrics_intersection_finite_of_sequential_regular
      f g h hf hg hh hf0 hgreg hhregular
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8 := by
  letI := triple_quadrics_intersection_finite_of_sequential_regular
    f g h hf hg hh hf0 hgreg hhregular
  exact triple_quadrics_intersection_length_eight
    f g h hf hg hh hf0
    (right_ne_zero_of_regular_mod_span_singleton
      (homogeneous_not_isUnit_of_pos_degree hf (by omega)) hgreg)
    (isRelPrime_of_regular_mod_span_singleton hf0 hgreg) hhregular

end

end PfaffianDescent
