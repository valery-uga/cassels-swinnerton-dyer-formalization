import AllCharacteristics.CycleDegrees
import PfaffianDescent.QuadraticSecant

/-!
# Secant descent for the support of a degree-four cycle

The support is presented by finite field extensions and actual nonzero cubic
zeros over those fields. The extensions may be inseparable. The corresponding
result for actual scheme cycles and finite closed subschemes is proved in
`AllCharacteristics.SchemeQuadraticDescent`. Construction of a lifted finite
subscheme remains a separate geometric obligation.
-/

open PfaffianDescent Module
open scoped BigOperators

namespace AllCharacteristics

/-- If points on a cubic form an effective family of total degree four, then
there is a base-field point or one of the supplied extensions has degree four.
The degree-two case is resolved by the characteristic-independent secant proof. -/
theorem cubic_point_or_quartic_of_degree_four_family
    {k ι : Type*} [Field k] (L : ι → Type*)
    [∀ i, Field (L i)] [∀ i, Algebra k (L i)] [∀ i, FiniteDimensional k (L i)]
    {n : ℕ} (c : Cubic k n) (s : Finset ι) (weight : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < weight i)
    (x : ∀ i, Vec (L i) n) (hx : ∀ i ∈ s, x i ≠ 0)
    (hc : ∀ i ∈ s, (c.map (algebraMap k (L i))).eval (x i) = 0)
    (hd : ∑ i ∈ s, weight i * finrank k (L i) = 4) :
    (∃ y : Vec k n, y ≠ 0 ∧ c.eval y = 0) ∨
      ∃ i ∈ s, finrank k (L i) = 4 := by
  obtain ⟨i, hi, hdeg⟩ := exists_degree_one_two_four_of_sum_four
    s weight (fun i => finrank k (L i)) hw hd
  rcases hdeg with h₁ | h₂ | h₄
  · exact Or.inl (cubic_degree_le_two_secant (by omega) c (x i) (hx i hi) (hc i hi))
  · exact Or.inl (cubic_degree_le_two_secant (by omega) c (x i) (hx i hi) (hc i hi))
  · exact Or.inr ⟨i, hi, h₄⟩

end AllCharacteristics
