import PfaffianDescent.MultivariateCubic
import Mathlib.Data.Finsupp.Multiset

/-!
# Cubic coefficient tensors without a characteristic restriction

Every degree-three monomial is a product of three variables, with repetition
allowed. Expanding a homogeneous polynomial in monomials therefore supplies a
cubic tensor over any commutative ring, including characteristics two and three.
This connects the characteristic-independent secant theorem to ordinary cubic
equations.
-/

open PfaffianDescent
open scoped BigOperators
namespace AllCharacteristics

/-- An exponent of total degree three is a sum of three variable exponents. -/
theorem cubic_exponent_eq_three_singles {σ : Type*} (d : σ →₀ ℕ) (hd : d.degree = 3) :
    ∃ i j l : σ, d = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single l 1 := by
  classical
  have hm : d.toMultiset.card = 3 := (Finsupp.card_toMultiset d).trans hd
  obtain ⟨i, j, l, h⟩ := Multiset.card_eq_three.mp hm
  refine ⟨i, j, l, ?_⟩
  apply (Multiset.toFinsupp.symm : (σ →₀ ℕ) ≃+ Multiset σ).injective
  change d.toMultiset =
    (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single l 1).toMultiset
  rw [h]
  simp only [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul,
    add_assoc, Multiset.singleton_add, Multiset.insert_eq_cons]

/-- The polynomial represented by a tensor supported at one ordered triple. -/
theorem cubic_toMvPolynomial_single {R : Type*} [CommRing R] {n : ℕ}
    (i j l : Fin n) (r : R) :
    Cubic.toMvPolynomial (Pi.single (i, j, l) r : Cubic R n) =
      MvPolynomial.C r * MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l := by
  classical
  rw [Cubic.toMvPolynomial, Finset.sum_eq_single (i, j, l)]
  · simp
  · intro a _ ha
    simp [Pi.single_eq_of_ne ha]
  · simp

/-- Every homogeneous cubic has a coefficient tensor over any commutative
ring. The proof does not divide by the degree or by factorials. -/
theorem homogeneous_cubic_has_tensor_any_characteristic
    {R : Type*} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : p.IsHomogeneous 3) :
    ∃ c : Cubic R n, c.toMvPolynomial = p := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    exact ⟨0, by simp [Cubic.toMvPolynomial]⟩
  | add p q _ _ ihp ihq =>
    obtain ⟨c, rfl⟩ := ihp
    obtain ⟨e, rfl⟩ := ihq
    refine ⟨c + e, ?_⟩
    simp only [Cubic.toMvPolynomial, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  | monomial d r hd =>
    have hd' : d.degree = 3 := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
    obtain ⟨i, j, l, h⟩ := cubic_exponent_eq_three_singles d hd'
    refine ⟨Pi.single (i, j, l) r, ?_⟩
    rw [cubic_toMvPolynomial_single]
    simp only [MvPolynomial.C_apply, MvPolynomial.X, MvPolynomial.monomial_mul,
      zero_add, mul_one, h]

/-- A nonzero solution of an ordinary homogeneous cubic over an extension of
degree at most two descends over every field, including inseparable extensions. -/
theorem homogeneous_cubic_degree_le_two_descent
    {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    {n : ℕ} (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (hd : Module.finrank k L ≤ 2) (x : Fin n → L) (hx : x ≠ 0)
    (he : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin n → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor_any_characteristic p hp
  rw [Cubic.eval_toMvPolynomial] at he
  obtain ⟨y, hy, hey⟩ := cubic_degree_le_two_secant hd c x hx he
  refine ⟨y, hy, ?_⟩
  change MvPolynomial.eval₂ (RingHom.id k) y c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact hey

end AllCharacteristics
