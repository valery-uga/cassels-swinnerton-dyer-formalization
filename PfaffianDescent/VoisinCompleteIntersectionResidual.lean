import PfaffianDescent.TripleCompleteIntersectionLength
import PfaffianDescent.TripleCompleteIntersectionToHypersurface
import PfaffianDescent.FiniteSchemeResidual
import PfaffianDescent.ReducedFiniteAlgebraFrobenius
import PfaffianDescent.FiniteEtaleSchemeFrobenius
import PfaffianDescent.VoisinRegularSequenceCriteria

/-!
# Residual lengths in Voisin's complete intersections

This combines the Koszul computations of the two complete-intersection
lengths with the annihilator-residual construction.  The only algebraic datum
left explicit is a Frobenius functional on the finite complete-intersection
algebra; later generic transversality (or the complete-intersection Gorenstein
theorem) supplies it.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A length-sixteen closed subscheme in a Frobenius intersection of three
regular cubics has annihilator residual of length eleven. -/
theorem triple_cubic_residual_rank_eleven
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16)
    (hfrob :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤),
        IsFrobeniusFunctional ell) :
    letI := triple_cubic_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := triple_cubic_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  have hX : AllCharacteristics.finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven
      f g h hf hg hh hf0 hg0 hrel hregular
  have hcomp := finite_scheme_residual_rank_complement
    i (toBase I) 27 16 hX hZ hfrob
  norm_num at hcomp ⊢
  exact hcomp

/- Prime avoidance is the geometric form of the regularity hypothesis used
above. -/
theorem triple_cubic_residual_rank_eleven_of_prime
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hprime : (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (havoid : h ∉ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel
        (third_equation_regular_of_span_isPrime f g h hprime havoid)
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16)
    (hfrob :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel
        (third_equation_regular_of_span_isPrime f g h hprime havoid)
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤),
        IsFrobeniusFunctional ell) :
    letI := triple_cubic_intersection_finite
      f g h hf hg hh hf0 hg0 hrel
      (third_equation_regular_of_span_isPrime f g h hprime havoid)
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 11 := by
  exact triple_cubic_residual_rank_eleven f g h hf hg hh hf0 hg0 hrel
    (third_equation_regular_of_span_isPrime f g h hprime havoid) i hZ hfrob

/-- For a reduced triple-cubic intersection in characteristic zero, the
Frobenius functional required above is supplied by the sum of the trace
functionals on its finite separable residue fields. -/
theorem triple_cubic_residual_rank_eleven_of_reduced
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [IsReduced Γ(scheme
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤)]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16) :
    letI := triple_cubic_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := triple_cubic_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  letI := finiteSchemeCoefficientAlgebra (toBase I)
  have hfinite := finiteSchemeCoefficient_finite (toBase I)
  apply triple_cubic_residual_rank_eleven
    f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact reducedFiniteAlgebra_exists_frobeniusFunctional

/-- A transverse (finite étale) triple-cubic intersection has residual
length eleven, with no separately supplied Frobenius datum. -/
theorem triple_cubic_residual_rank_eleven_of_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16) :
    letI := triple_cubic_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := triple_cubic_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  apply triple_cubic_residual_rank_eleven
    f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact finiteEtaleScheme_exists_frobeniusFunctional (toBase I)

/-- The residual to a length-sixteen subscheme in a finite étale triple-cubic
intersection supplies an actual effective zero-cycle of degree eleven on that
intersection. -/
theorem exists_effectiveZeroCycle_degree_eleven_of_triple_cubic_residual_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle
        (scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)),
      AllCharacteristics.EffectiveZeroCycle.degree
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) r = 11 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := triple_cubic_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  obtain ⟨r, hr⟩ := AllCharacteristics.exists_effectiveZeroCycle_of_finite_closed_subscheme
    (finiteClosedResidualι i (toBase I)) (toBase I)
  refine ⟨r, ?_⟩
  exact hr.trans (triple_cubic_residual_rank_eleven_of_etale
    f g h hf hg hh hf0 hg0 hrel hregular i hZ)

/-- Pushing the triple-cubic residual through its closed immersion gives an
effective degree-eleven zero-cycle on the original cubic hypersurface. -/
theorem exists_effectiveZeroCycle_degree_eleven_on_cubic_of_triple_cubic_residual_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hh : h.IsHomogeneous 3) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := triple_cubic_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 16) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) r = 11 := by
  obtain ⟨r, hr⟩ := exists_effectiveZeroCycle_degree_eleven_of_triple_cubic_residual_etale
    f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact exists_effectiveZeroCycle_on_hypersurface_of_triple f g h hf hg hh 11 r hr

/-- A length-eight closed subscheme in a Frobenius intersection of a cubic
and two regular quadrics has annihilator residual of length four. -/
theorem cubic_two_quadrics_residual_rank_four
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤),
        IsFrobeniusFunctional ell) :
    letI := cubic_two_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := cubic_two_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  have hX : AllCharacteristics.finiteSchemeRank (toBase I) = 12 :=
    cubic_two_quadrics_intersection_length_twelve
      f g h hf hg hh hf0 hg0 hrel hregular
  have hcomp := finite_scheme_residual_rank_complement
    i (toBase I) 12 8 hX hZ hfrob
  norm_num at hcomp ⊢
  exact hcomp

/- The cubic-two-quadric residual also accepts the prime-avoidance form of
regularity. -/
theorem cubic_two_quadrics_residual_rank_four_of_prime
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hprime : (Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (havoid : h ∉ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel
        (third_equation_regular_of_span_isPrime f g h hprime havoid)
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel
        (third_equation_regular_of_span_isPrime f g h hprime havoid)
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤),
        IsFrobeniusFunctional ell) :
    letI := cubic_two_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel
      (third_equation_regular_of_span_isPrime f g h hprime havoid)
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 4 := by
  exact cubic_two_quadrics_residual_rank_four f g h hf hg hh hf0 hg0 hrel
    (third_equation_regular_of_span_isPrime f g h hprime havoid) i hZ hfrob

/-- For a reduced cubic-two-quadric intersection in characteristic zero,
the trace pairing supplies the Frobenius functional and the residual has
length four. -/
theorem cubic_two_quadrics_residual_rank_four_of_reduced
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [IsReduced Γ(scheme
      (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh), ⊤)]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    letI := cubic_two_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := cubic_two_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  letI := finiteSchemeCoefficientAlgebra (toBase I)
  have hfinite := finiteSchemeCoefficient_finite (toBase I)
  apply cubic_two_quadrics_residual_rank_four
    f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact reducedFiniteAlgebra_exists_frobeniusFunctional

/-- A transverse (finite étale) cubic-two-quadric intersection has residual
length four, with no separately supplied Frobenius datum. -/
theorem cubic_two_quadrics_residual_rank_four_of_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    letI := cubic_two_quadrics_intersection_finite
      f g h hf hg hh hf0 hg0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (finiteClosedResidualι i
          (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) ≫
        toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := cubic_two_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  apply cubic_two_quadrics_residual_rank_four
    f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact finiteEtaleScheme_exists_frobeniusFunctional (toBase I)

/-- The residual to a length-eight subscheme in a finite étale
cubic--quadric--quadric intersection supplies an actual effective zero-cycle
of degree four on that intersection. -/
theorem exists_effectiveZeroCycle_degree_four_of_cubic_two_quadrics_residual_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle
        (scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)),
      AllCharacteristics.EffectiveZeroCycle.degree
        (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) r = 4 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  letI := cubic_two_quadrics_intersection_finite
    f g h hf hg hh hf0 hg0 hrel hregular
  obtain ⟨r, hr⟩ := AllCharacteristics.exists_effectiveZeroCycle_of_finite_closed_subscheme
    (finiteClosedResidualι i (toBase I)) (toBase I)
  refine ⟨r, ?_⟩
  exact hr.trans (cubic_two_quadrics_residual_rank_four_of_etale
    f g h hf hg hh hf0 hg0 hrel hregular i hZ)

/-- Pushing the cubic--quadric--quadric residual through its closed immersion
gives an effective degree-four zero-cycle on the cubic hypersurface. -/
theorem exists_effectiveZeroCycle_degree_four_on_cubic_of_cubic_two_quadrics_residual_etale
    [CharZero K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hg : g.IsHomogeneous 2)
    (hh : h.IsHomogeneous 2) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hrel : IsRelPrime f g)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      h * x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({f, g} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion i]
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    (hZ :
      letI := cubic_two_quadrics_intersection_finite
        f g h hf hg hh hf0 hg0 hrel hregular
      AllCharacteristics.finiteSchemeRank
        (i ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    ∃ r : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) r = 4 := by
  obtain ⟨r, hr⟩ :=
    exists_effectiveZeroCycle_degree_four_of_cubic_two_quadrics_residual_etale
      f g h hf hg hh hf0 hg0 hrel hregular i hZ
  exact exists_effectiveZeroCycle_on_hypersurface_of_triple f g h hf hg hh 4 r hr

end

end PfaffianDescent
