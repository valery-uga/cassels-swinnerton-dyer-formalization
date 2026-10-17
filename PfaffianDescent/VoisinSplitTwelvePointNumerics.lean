import PfaffianDescent.VoisinStandardFourLineWitness
import PfaffianDescent.VoisinTwelvePointQuadraticKernel
import PfaffianDescent.VoisinCompleteIntersectionResidual
import PfaffianDescent.VoisinFiniteAlgebraRationalPointSplit

/-!
# Numerical structure of a split twelve-point witness

The explicit split quadrics over a characteristic-zero field give an actual
finite cubic--quadric--quadric intersection of length twelve. Their
independence identifies the quadratic coordinate quotient as dimension eight.
Reducedness and selection of eight geometric points are separate questions.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Independence of homogeneous quadrics as polynomials is the same
independence required by the quadratic-restriction theorem. -/
theorem homogeneous_quadric_pair_linearIndependent_of_polynomials
    {K : Type u} [Field K]
    (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hli : LinearIndependent K ![q, r]) :
    LinearIndependent K
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply (Fintype.linearIndependent_iff.mp hli) c
  have hv := congrArg Subtype.val hc
  have hpoint (i : Fin 2) :
      ((![⟨q, hq⟩, ⟨r, hr⟩] i : homogeneousSubmodule (Fin 4) K 2) :
        MvPolynomial (Fin 4) K) = ![q, r] i := by
    fin_cases i <;> rfl
  simpa only [Submodule.coe_sum, Submodule.coe_smul,
    Submodule.coe_zero, hpoint] using hv

/-- Every smooth cubic over a characteristic-zero field has an explicit
split complete intersection of length twelve, whose degree-two coordinate
quotient has rank eight. -/
theorem exists_split_twelve_point_witness_with_quadratic_quotient_eight
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      ∃ hfinite : IsFinite (toBase
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)),
        letI : IsFinite (toBase
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := hfinite
        q ≠ 0 ∧ IsRelPrime p q ∧
        (∀ F : MvPolynomial (Fin 4) K,
          r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        LinearIndependent K ![q, r] ∧
        LinearIndependent K
          ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 2), ⟨r, hr⟩] ∧
        finiteSchemeRank (toBase
          (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12 ∧
        Module.finrank K
          (grading (tripleCompleteIntersectionHomogeneousIdeal
            p q r hp hq hr) 2) = 8 := by
  obtain ⟨q, r, hq, hr, hq0, hli, hrel, hregular⟩ :=
    exists_split_quadric_pair_regular_relprime_over_charZero_of_smooth
      p hp hp0
  have hfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
    cubic_two_quadrics_intersection_finite
      p q r hp hq hr hp0 hq0 hrel hregular
  refine ⟨q, r, hq, hr, hfinite, hq0, hrel, hregular, hli,
    homogeneous_quadric_pair_linearIndependent_of_polynomials q r hq hr hli,
    ?_, ?_⟩
  · exact cubic_two_quadrics_intersection_length_twelve
      p q r hp hq hr hp0 hq0 hrel hregular
  · exact cubic_two_quadric_quadratic_quotient_finrank_eq_eight
      p q r hp hq hr hli

/-- For any length-twelve cubic--quadric--quadric intersection, twelve
distinct rational scheme points force the actual projective intersection to
be étale. This is the precise point-counting target for the split witness. -/
theorem cubic_two_quadric_etale_of_twelve_distinct_rational_points
    {K : Type u} [Field K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [hfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hrank : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12)
    (x : Fin 12 → (Spec (.of K) ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)))
    (hxbase : ∀ i, (x i) ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      Spec.map (CommRingCat.ofHom (RingHom.id K)))
    (hxinj : Function.Injective x) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  exact finiteScheme_etale_of_full_rational_points
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    x hxbase hxinj hrank

/-- The four-times-three indexing produced by split line sections is
equivalent to `Fin 12`, so its rational-point family saturates the
length-twelve intersection just as a directly indexed family does. -/
theorem cubic_two_quadric_etale_of_four_triples_rational_points
    {K : Type u} [Field K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [hfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hrank : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12)
    (x : (Fin 2 × Fin 2 × Fin 3) → (Spec (.of K) ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)))
    (hxbase : ∀ i, (x i) ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) =
      Spec.map (CommRingCat.ofHom (RingHom.id K)))
    (hxinj : Function.Injective x) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  exact cubic_two_quadric_etale_of_twelve_distinct_rational_points
    p q r hp hq hr hrank (x ∘ e) (fun i => hxbase (e i))
    (hxinj.comp e.injective)

/-- Vanishing of the three defining forms is exactly what is needed for
vanishing of every element of their homogeneous complete-intersection ideal. -/
theorem tripleCompleteIntersection_vector_zero_of_generators
    {K : Type u} [Field K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (v : Fin 4 → K)
    (hpv : p.eval v = 0) (hqv : q.eval v = 0)
    (hrv : r.eval v = 0) :
    ∀ f ∈ (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal,
      f.eval v = 0 := by
  have hspan : Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id K) v) := by
    rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · simpa using hpv
    · simpa using hqv
    · simpa using hrv
  intro f hf
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal] at hf
  simpa using hspan hf

/-- A sheared four-line root presentation with twelve distinct projective
directions proves étaleness of the actual length-twelve intersection. The
geometric separability and equation-vanishing premises are kept explicit. -/
theorem cubic_two_quadric_etale_of_sheared_four_line_roots
    {K : Type u} [Field K] [Infinite K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [hfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hrank : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12)
    (a : Fin 4 → K) (ha0 : a 0 ≠ 0)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → K)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hform : ∀ i j k, ∃ t : K, x i j k = t • a + lineDirection i j)
    (hzero : ∀ i j k,
      ∀ f ∈ (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal,
        f.eval (x i j k) = 0) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  obtain ⟨t, htbase, htinj⟩ :=
    exists_twelve_distinct_scheme_points_of_sheared_line_roots
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)
      a ha0 x hinj hform hzero
  exact cubic_two_quadric_etale_of_four_triples_rational_points
    p q r hp hq hr hrank t htbase htinj

/-- The same conditional endpoint stated using only the three defining
polynomial evaluations at each displayed line root. -/
theorem cubic_two_quadric_etale_of_sheared_four_line_root_equations
    {K : Type u} [Field K] [Infinite K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    [hfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hrank : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) = 12)
    (a : Fin 4 → K) (ha0 : a 0 ≠ 0)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → K)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hform : ∀ i j k, ∃ t : K, x i j k = t • a + lineDirection i j)
    (hroots : ∀ i j k,
      p.eval (x i j k) = 0 ∧ q.eval (x i j k) = 0 ∧
        r.eval (x i j k) = 0) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  apply cubic_two_quadric_etale_of_sheared_four_line_roots
    p q r hp hq hr hrank a ha0 x hinj hform
  intro i j k
  exact tripleCompleteIntersection_vector_zero_of_generators
    p q r hp hq hr (x i j k)
      (hroots i j k).1 (hroots i j k).2.1 (hroots i j k).2.2

end PfaffianDescent
