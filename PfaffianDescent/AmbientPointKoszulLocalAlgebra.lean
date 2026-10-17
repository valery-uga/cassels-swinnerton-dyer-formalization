import PfaffianDescent.ThreeGeneratorKoszul
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.PointGlobalTraceKoszulCartierHomotopy
import AllCharacteristics.AmbientChartPresentation
import AllCharacteristics.PolynomialCoordinateOne
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Data.Finsupp.Weight

/-! # Local algebra for the standard point of projective three-space

The point-containing chart has three independent polynomial coordinates.
This file proves their regularity and the algebraic Koszul exactness without
assuming any global trace or duality statement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u

/-- Evaluation at the affine origin has precisely the variable ideal as kernel. -/
theorem ambientPointKoszul_eval_zero_ker
    {R σ : Type*} [CommRing R] :
    RingHom.ker (eval₂Hom (RingHom.id R) (0 : σ → R)) = idealOfVars σ R := by
  ext p
  change eval (0 : σ → R) p = 0 ↔ p ∈ idealOfVars σ R
  rw [eval_zero, constantCoeff_eq, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  constructor
  · intro hp m hm
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    simpa [hm0] using hp
  · intro hp
    exact hp 0 (by simp)

/-- A unit-ideal relation contracts the three-generator Koszul complex,
giving its exactness and both endpoint properties over any commutative ring. -/
theorem ambientPointKoszul_exact_of_unit_relation
    {R : Type*} [CommRing R] (f g h a b c : R)
    (hunit : f * a + g * b + h * c = 1) :
    Function.Injective (threeGeneratorFirst f g h) ∧
      LinearMap.range (threeGeneratorFirst f g h) = LinearMap.ker (threeGeneratorMiddle f g h) ∧
      LinearMap.range (threeGeneratorMiddle f g h) = LinearMap.ker (threeGeneratorLast f g h) ∧
      Function.Surjective (threeGeneratorLast f g h) := by
  have hleft (x : R) :
      pointGlobalTraceCartierHomotopyTwo a b c (threeGeneratorFirst f g h x) = x := by
    simpa [hunit] using pointGlobalTraceCartierHomotopy_degreeThree f g h a b c x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  · apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_middle_comp_first f g h)
    · intro x hx
      have hx' : threeGeneratorMiddle f g h x = 0 := hx
      refine ⟨pointGlobalTraceCartierHomotopyTwo a b c x, ?_⟩
      simpa [hx', hunit] using pointGlobalTraceCartierHomotopy_degreeTwo f g h a b c x
  · apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr (threeGenerator_last_comp_middle f g h)
    · intro x hx
      have hx' : threeGeneratorLast f g h x = 0 := hx
      refine ⟨pointGlobalTraceCartierHomotopyOne a b c x, ?_⟩
      simpa [hx', hunit] using pointGlobalTraceCartierHomotopy_degreeOne f g h a b c x
  · intro x
    refine ⟨pointGlobalTraceCartierHomotopyZero a b c x, ?_⟩
    simpa [hunit] using pointGlobalTraceCartierHomotopy_degreeZero f g h a b c x

/-- One invertible equation makes the three-generator Koszul complex exact. -/
theorem ambientPointKoszul_exact_of_any_unit
    {R : Type*} [CommRing R] (f g h : R)
    (hu : IsUnit f ∨ IsUnit g ∨ IsUnit h) :
    Function.Injective (threeGeneratorFirst f g h) ∧
      LinearMap.range (threeGeneratorFirst f g h) = LinearMap.ker (threeGeneratorMiddle f g h) ∧
      LinearMap.range (threeGeneratorMiddle f g h) = LinearMap.ker (threeGeneratorLast f g h) ∧
      Function.Surjective (threeGeneratorLast f g h) := by
  rcases hu with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ambientPointKoszul_exact_of_unit_relation _ _ _ (↑v⁻¹) 0 0 (by simp)
  · exact ambientPointKoszul_exact_of_unit_relation _ _ _ 0 (↑v⁻¹) 0 (by simp)
  · exact ambientPointKoszul_exact_of_unit_relation _ _ _ 0 0 (↑v⁻¹) (by simp)

/-- Multiplication by a variable outside a set of variables is injective
modulo their generated ideal. -/
theorem ambientPointKoszul_variable_regular_mod_span
    {R σ : Type*} [CommRing R] (s : Set σ) (k : σ) (hk : k ∉ s)
    (p : MvPolynomial σ R)
    (hp : X k * p ∈ Ideal.span (X '' s : Set (MvPolynomial σ R))) :
    p ∈ Ideal.span (X '' s : Set (MvPolynomial σ R)) := by
  classical
  rw [mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hm' : Finsupp.single k 1 + m ∈ (X k * p).support := by
    rw [support_X_mul]
    exact Finset.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨i, hi, hmi⟩ := hp _ hm'
  refine ⟨i, hi, ?_⟩
  have hik : i ≠ k := by
    intro h
    exact hk (h ▸ hi)
  simpa [Finsupp.single_apply, hik.symm] using hmi

/-- The third standard affine coordinate is regular modulo the first two. -/
theorem ambientPointKoszul_polynomial_third_regular
    {K : Type u} [Field K] (p : MvPolynomial (Fin 3) K)
    (hp : X 2 * p ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) K))) :
    p ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 3) K)) := by
  have h := ambientPointKoszul_variable_regular_mod_span
    ({0, 1} : Set (Fin 3)) 2 (by decide) p
  have hp' : X (2 : Fin 3) * p ∈
      Ideal.span (X '' ({0, 1} : Set (Fin 3)) : Set (MvPolynomial (Fin 3) K)) := by
    simpa only [Set.image_pair] using hp
  simpa only [Set.image_pair] using h hp'

/-- The first two standard affine coordinates are relatively prime. -/
theorem ambientPointKoszul_polynomial_relPrime
    {K : Type u} [Field K] :
    IsRelPrime (X 0 : MvPolynomial (Fin 3) K) (X 1) :=
  isRelPrime_of_prime_not_dvd (X_prime (i := (0 : Fin 3)) (R := K)) (by simp)

/-- Algebraic exactness at degree two on the standard point chart. -/
theorem ambientPointKoszul_polynomial_exact_middle
    {K : Type u} [Field K] :
    LinearMap.range (threeGeneratorFirst (X 0 : MvPolynomial (Fin 3) K) (X 1) (X 2)) =
      LinearMap.ker (threeGeneratorMiddle (X 0) (X 1) (X 2)) :=
  threeGenerator_exact_middle (by simp) (by simp) ambientPointKoszul_polynomial_relPrime

/-- Algebraic exactness at degree one on the standard point chart. -/
theorem ambientPointKoszul_polynomial_exact_last
    {K : Type u} [Field K] :
    LinearMap.range (threeGeneratorMiddle (X 0 : MvPolynomial (Fin 3) K) (X 1) (X 2)) =
      LinearMap.ker (threeGeneratorLast (X 0) (X 1) (X 2)) :=
  threeGenerator_exact_last (by simp) ambientPointKoszul_polynomial_relPrime
    ambientPointKoszul_polynomial_third_regular

end PfaffianDescent
