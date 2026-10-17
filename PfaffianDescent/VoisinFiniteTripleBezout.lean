import PfaffianDescent.TripleQuadricsGlobalThirdRegularity
import PfaffianDescent.TripleCompleteIntersectionLength

/-!
# Bézout length from finite nonempty triple intersections

The existing finite-intersection regularity theorems recover the sequential
regularity hypotheses required by the complete-intersection Hilbert
calculation. Thus a finite nonempty cubic--quadric--quadric projective
intersection has length twelve without separately assuming regularity.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicTwoQuadrics_finite_nonempty_rank_twelve
    {F : Type u} [Field F] [Infinite F]
    (p q r : MvPolynomial (Fin 4) F)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      p q r hp hq hr))) :
    AllCharacteristics.finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12 := by
  have hlin := tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty
    p q r hp hq hr hX
  have hp0 : p ≠ 0 := by
    intro h
    apply hlin.ne_zero 0
    simp [h]
  have hq0 : q ≠ 0 := by
    intro h
    apply hlin.ne_zero 1
    simp [h]
  have hrel : IsRelPrime p q :=
    tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
      p q r hp hq hr (by decide) hX
  have hregular : ∀ x : MvPolynomial (Fin 4) F,
      r * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) F)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) F)) := by
    intro x hx
    exact third_regular_of_finite_degrees p q r hp hq hr
      (by decide) (by decide) hX x hx
  exact cubic_two_quadrics_intersection_length_twelve
    p q r hp hq hr hp0 hq0 hrel hregular

end PfaffianDescent
