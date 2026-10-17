import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import PfaffianDescent.VoisinGenericFreenessLeadingMonomials

/-!
# Eventual affine growth for finite standard-monomial slices

When the standard exponents of a one-dimensional projective scheme have
finite fibres over two free coordinates, each fibre contributes a tail of
monomials. This arithmetic lemma records the eventual affine growth of a
finite collection of such tails. The remaining geometric work is to prove
that a Gröbner basis for Voisin's varying fixed curve gives precisely this
finite-fibre description.
-/

namespace PfaffianDescent

open scoped BigOperators
open scoped MonomialOrder

/-- A fixed finite set of thresholds contributes an eventually affine
function: after the largest threshold, increasing the degree by `k` adds
exactly `k` monomials in each fibre. -/
theorem finiteThresholdTail_eventually_affine
    (T : Finset ℕ) (N : ℕ)
    (hN : ∀ t ∈ T, t ≤ N) (k : ℕ) :
    (∑ t ∈ T, (N + k + 1 - t)) =
      T.card * k + ∑ t ∈ T, (N + 1 - t) := by
  calc
    (∑ t ∈ T, (N + k + 1 - t)) =
        ∑ t ∈ T, (k + (N + 1 - t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          have htn := hN t ht
          omega
    _ = (∑ t ∈ T, k) + ∑ t ∈ T, (N + 1 - t) := by
          rw [Finset.sum_add_distrib]
    _ = T.card * k + ∑ t ∈ T, (N + 1 - t) := by
          simp [Nat.mul_comm]

/-- The same calculation with a tail indexed by the exponents of two
coordinates. For each fixed `(a,b)`, the other two coordinates contribute
`n + 1 - (a + b)` monomials in degree `n`. -/
theorem finiteTwoCoordinateTail_eventually_affine
    (T : Finset (ℕ × ℕ)) (N : ℕ)
    (hN : ∀ t ∈ T, t.1 + t.2 ≤ N) (k : ℕ) :
    (∑ t ∈ T, (N + k + 1 - (t.1 + t.2))) =
      T.card * k + ∑ t ∈ T, (N + 1 - (t.1 + t.2)) := by
  calc
    (∑ t ∈ T, (N + k + 1 - (t.1 + t.2))) =
        ∑ t ∈ T, (k + (N + 1 - (t.1 + t.2))) := by
          apply Finset.sum_congr rfl
          intro t ht
          have htn := hN t ht
          omega
    _ = (∑ t ∈ T, k) + ∑ t ∈ T, (N + 1 - (t.1 + t.2)) := by
          rw [Finset.sum_add_distrib]
    _ = T.card * k + ∑ t ∈ T, (N + 1 - (t.1 + t.2)) := by
          simp [Nat.mul_comm]

/-- A pure-power leading monomial bounds that coordinate in every standard
exponent. -/
theorem standardExponents_coordinate_lt_of_purePower
    {F : Type*} [Field F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) (i : Fin 4) (r : ℕ)
    (hpow : (MvPolynomial.X i) ^ r ∈ G)
    (e : Fin 4 →₀ ℕ) (he : e ∈ standardExponents m G) :
    e i < r := by
  have hdegree : m.degree
      ((MvPolynomial.X i : MvPolynomial (Fin 4) F) ^ r) =
        Finsupp.single i r := by
    rw [MonomialOrder.degree_pow, MonomialOrder.degree_X]
    simp
  by_contra hlt
  have hle : r ≤ e i := Nat.le_of_not_gt hlt
  have hdiv : Finsupp.single i r ≤ e := Finsupp.single_le_iff.mpr hle
  exact he ((MvPolynomial.X i) ^ r) hpow (hdegree ▸ hdiv)

/-- Two pure-power leading monomials make the standard exponents finite over
the other two coordinates: their projection to the selected coordinate pair
lies in a finite rectangle. This is the Gröbner-theoretic finite-tail
condition used by the preceding counting lemma. -/
theorem standardExponents_twoCoordinates_in_finiteRectangle
    {F : Type*} [Field F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) (i j : Fin 4)
    (r s : ℕ)
    (hi : (MvPolynomial.X i) ^ r ∈ G)
    (hj : (MvPolynomial.X j) ^ s ∈ G)
    (e : Fin 4 →₀ ℕ) (he : e ∈ standardExponents m G) :
    e i < r ∧ e j < s := by
  exact ⟨standardExponents_coordinate_lt_of_purePower m G i r hi e he,
    standardExponents_coordinate_lt_of_purePower m G j s hj e he⟩

/-- The projection of the standard-exponent set to two coordinates is
finite whenever the leading set contains pure powers in those coordinates. -/
theorem standardExponents_twoCoordinateProjection_finite
    {F : Type*} [Field F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) (i j : Fin 4)
    (r s : ℕ) (hi : (MvPolynomial.X i) ^ r ∈ G)
    (hj : (MvPolynomial.X j) ^ s ∈ G) :
    {t : ℕ × ℕ | ∃ e ∈ standardExponents m G, t = (e i, e j)}.Finite := by
  have hrectangle : {t : ℕ × ℕ | t.1 < r ∧ t.2 < s}.Finite :=
    (Set.finite_Iio r).prod (Set.finite_Iio s)
  apply hrectangle.subset
  intro t ht
  obtain ⟨e, he, rfl⟩ := ht
  exact standardExponents_twoCoordinates_in_finiteRectangle m G i j r s
    hi hj e he

/-- If two coordinate exponents are bounded by pure powers, the number of
standard exponents of total degree `n` is at most linear in `n`. The map
records the two bounded coordinates and one free coordinate; the final
coordinate is determined by the total degree. -/
theorem standardExponents_degreeSlice_card_le
    {F : Type*} [Field F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) (r s n : ℕ)
    (hi : (MvPolynomial.X (2 : Fin 4)) ^ r ∈ G)
    (hj : (MvPolynomial.X (3 : Fin 4)) ^ s ∈ G) :
    let α := {e : Fin 4 →₀ ℕ //
      e ∈ standardExponents m G ∧ e.sum (fun _ x => x) = n}
    Nat.card α ≤
      Nat.card {t : ℕ × ℕ //
        ∃ e ∈ standardExponents m G, t = (e 2, e 3)} * (n + 1) := by
  classical
  let α := {e : Fin 4 →₀ ℕ //
    e ∈ standardExponents m G ∧ e.sum (fun _ x => x) = n}
  let P := {t : ℕ × ℕ //
    ∃ e ∈ standardExponents m G, t = (e 2, e 3)}
  have hP : {t : ℕ × ℕ | ∃ e ∈ standardExponents m G,
      t = (e 2, e 3)}.Finite :=
    standardExponents_twoCoordinateProjection_finite m G 2 3 r s hi hj
  letI : Finite P := hP.to_subtype
  let code : α → P × Fin (n + 1) := fun z =>
      (⟨(z.1 2, z.1 3), ⟨z.1, z.2.1, rfl⟩⟩,
      ⟨z.1 0, by
        have hle : z.1 0 ≤ z.1.sum (fun _ x => x) := by
          simpa using Finsupp.single_eval_le_sum (f := z.1)
            (g := fun x : ℕ => x) (by simp)
            (fun x => Nat.zero_le x) (0 : Fin 4)
        rw [z.2.2] at hle
        exact Nat.lt_succ_of_le hle⟩)
  have hcode : Function.Injective code := by
    intro z w h
    apply Subtype.ext
    have hp := congrArg Prod.fst h
    have htail := congrArg Subtype.val hp
    have h0 : z.1 0 = w.1 0 := by
      exact congrArg Fin.val (congrArg Prod.snd h)
    have h2 : z.1 2 = w.1 2 := congrArg Prod.fst htail
    have h3 : z.1 3 = w.1 3 := congrArg Prod.snd htail
    have hsum : z.1.sum (fun _ x => x) = w.1.sum (fun _ x => x) :=
      z.2.2.trans w.2.2.symm
    have hsum' : z.1 0 + z.1 1 + z.1 2 + z.1 3 =
        w.1 0 + w.1 1 + w.1 2 + w.1 3 := by
      convert (by simpa [Finsupp.sum_fintype, Fin.sum_univ_succ] using hsum) using 1 <;>
        ring
    have hsum'' := hsum'
    ring_nf at hsum''
    have h1 : z.1 1 = w.1 1 := by
      rw [h0, h2, h3] at hsum''
      omega
    apply Finsupp.ext
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hcard := Nat.card_le_card_of_injective code hcode
  simpa [code, P, Nat.card_eq_fintype_card, Fintype.card_prod] using hcard

/-- A finite algebra over a chosen coordinate subalgebra makes each of the
remaining coordinates satisfy a monic relation over it. In a graded Noether
normalization argument, these relations are the source of pure-power leading
terms after the normalizing coordinates are placed below the remaining ones
in a block monomial order. -/
theorem exists_monic_relations_of_finite_algebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] (x y : A) :
    ∃ f g : Polynomial R,
      f.Monic ∧ Polynomial.aeval x f = 0 ∧
      g.Monic ∧ Polynomial.aeval y g = 0 := by
  obtain ⟨f, hfm, hfx⟩ := IsIntegral.of_finite R x
  obtain ⟨g, hgm, hgy⟩ := IsIntegral.of_finite R y
  exact ⟨f, g, hfm, hfx, hgm, hgy⟩

end PfaffianDescent
