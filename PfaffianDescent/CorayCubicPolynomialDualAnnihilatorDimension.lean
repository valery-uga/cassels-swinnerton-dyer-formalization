import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.FrameDimensionIdentity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The actual cubic-multiplication dual annihilator in four-variable
homogeneous polynomials. All spaces and maps retain their original K action.
This is the algebraic count needed after the genuine cubic cohomology boundary
has been shown to land in this annihilator. It does not assert that geometric
factorization or an intrinsic H¹ bound. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The literal polynomial multiplication, with only its homogeneous degree
index rewritten. The existing cubicSurfaceRelation has value b*p. -/
def cubicPolynomialMultiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) : S (n - 4) →ₗ[K] S (n - 1) :=
  (LinearEquiv.ofEq (S ((n - 4) + 3)) (S (n - 1))
    (congrArg (MvPolynomial.homogeneousSubmodule (Fin 4) K)
      (show (n - 4) + 3 = n - 1 by omega))).toLinearMap.comp
    (cubicSurfaceRelation p hp (n - 4))

/-- The degree-index transport preserves the actual underlying polynomial. -/
theorem cubicPolynomialMultiplication_coe
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) (b : S (n - 4)) :
    (cubicPolynomialMultiplication p hp n hn b : MvPolynomial (Fin 4) K) =
      (b : MvPolynomial (Fin 4) K) * p := rfl

/-- The SAME multiplication expressed in the left-multiplication convention
of the all-degree polynomial residue naturality theorem. -/
theorem cubicPolynomialMultiplication_apply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) (b : S (n - 4)) :
    cubicPolynomialMultiplication p hp n hn b =
      ⟨p * (b : MvPolynomial (Fin 4) K), by
        simpa only [MvPolynomial.mem_homogeneousSubmodule,
          show 3 + (n - 4) = n - 1 by omega] using hp.mul b.2⟩ := by
  apply Subtype.ext
  rw [cubicPolynomialMultiplication_coe, mul_comm]

/-- Cancellation by the actual nonzero cubic proves injectivity. -/
theorem cubicPolynomialMultiplication_injective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (cubicPolynomialMultiplication p hp n hn) := by
  intro a b hab
  apply cubicSurfaceRelation_injective p hp hp0 (n - 4)
  apply Subtype.ext
  change (a : MvPolynomial (Fin 4) K) * p = (b : MvPolynomial (Fin 4) K) * p
  have h := congrArg Subtype.val hab
  simpa only [cubicPolynomialMultiplication_coe] using h

/-- The subspace consists of the actual functionals on S_(n-1) which vanish
on the image of this literal polynomial multiplication. -/
abbrev cubicPolynomialDualAnnihilator
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) :=
  (LinearMap.range (cubicPolynomialMultiplication p hp n hn)).dualAnnihilator

/-- No finiteness certificate: homogeneousSubmodule_finite is derived from
actual finite generation, and finite duals and their subspaces are finite. -/
theorem cubicPolynomialDualAnnihilator_finite
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) :
    Module.Finite K (cubicPolynomialDualAnnihilator p hp n hn) := by
  infer_instance

/-- A direct criterion using the actual multiplication map. -/
theorem mem_cubicPolynomialDualAnnihilator_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) (phi : Module.Dual K (S (n - 1))) :
    phi ∈ cubicPolynomialDualAnnihilator p hp n hn ↔
      ∀ b : S (n - 4), phi (cubicPolynomialMultiplication p hp n hn b) = 0 := by
  change phi ∈ (LinearMap.range (cubicPolynomialMultiplication p hp n hn)).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h b
    exact h _ ⟨b, rfl⟩
  · intro h v hv
    obtain ⟨b, rfl⟩ := hv
    exact h b

/-- The literal p*b criterion, ready for the genuine residue naturality
calculation; its scalar action and polynomial are unchanged. -/
theorem mem_cubicPolynomialDualAnnihilator_iff_multiples
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) (phi : Module.Dual K (S (n - 1))) :
    phi ∈ cubicPolynomialDualAnnihilator p hp n hn ↔
      ∀ b : S (n - 4), phi ⟨p * (b : MvPolynomial (Fin 4) K), by
        simpa only [MvPolynomial.mem_homogeneousSubmodule,
          show 3 + (n - 4) = n - 1 by omega] using hp.mul b.2⟩ = 0 := by
  rw [mem_cubicPolynomialDualAnnihilator_iff]
  simp only [cubicPolynomialMultiplication_apply]

/-- This annihilator is also the actual kernel of precomposition by p. -/
theorem cubicPolynomialMultiplication_dualMap_ker
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 4 ≤ n) :
    LinearMap.ker (cubicPolynomialMultiplication p hp n hn).dualMap =
      cubicPolynomialDualAnnihilator p hp n hn := by
  exact (cubicPolynomialMultiplication p hp n hn).ker_dualMap_eq_dualAnnihilator_range

/-- Injectivity computes the dimension of the actual multiplication image. -/
theorem cubicPolynomialMultiplication_range_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    finrank K (LinearMap.range (cubicPolynomialMultiplication p hp n hn)) =
      (n - 1).choose 3 := by
  rw [LinearMap.finrank_range_of_inj
    (cubicPolynomialMultiplication_injective p hp hp0 n hn),
    four_variable_homogeneous_finrank,
    show (n - 4) + 3 = n - 1 by omega]

/-- Genuine dimension of the dual annihilator, with no assumed dimension. -/
theorem cubicPolynomialDualAnnihilator_finrank_choose
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    finrank K (cubicPolynomialDualAnnihilator p hp n hn) =
      (n + 2).choose 3 - (n - 1).choose 3 := by
  have hsum :
      finrank K (LinearMap.range (cubicPolynomialMultiplication p hp n hn)) +
        finrank K (cubicPolynomialDualAnnihilator p hp n hn) =
          finrank K (S (n - 1)) :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq
      (LinearMap.range (cubicPolynomialMultiplication p hp n hn))
  rw [cubicPolynomialMultiplication_range_finrank p hp hp0 n hn,
    four_variable_homogeneous_finrank,
    show (n - 1) + 3 = n + 2 by omega] at hsum
  omega

private theorem twice_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  rw [show Nat.factorial 2 = 2 by decide] at h
  simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one, mul_comm] using h.symm

/-- The exact arithmetic, including the natural-number subtraction. -/
theorem cubicPolynomialAnnihilator_choose_difference
    (n : ℕ) (hn : 4 ≤ n) :
    (n + 2).choose 3 - (n - 1).choose 3 = 1 + 3 * n.choose 2 := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 4 := ⟨n - 4, by omega⟩
  have hbig := six_mul_choose_three (d + 3)
  have hsmall := six_mul_choose_three d
  have htwo := twice_choose_two (d + 4)
  have hdegree : d + 4 - 1 = d + 3 := by omega
  rw [hdegree] at htwo
  simp only [Nat.add_assoc] at hbig
  have hsum :
      (d + 6).choose 3 = (d + 3).choose 3 + 1 + 3 * (d + 4).choose 2 := by
    nlinarith
  rw [hdegree, show (d + 4) + 2 = d + 6 by omega]
  omega

/-- The requested integer formula, proved by exact division of an even
product rather than by replacing the polynomial space with a dimension. -/
theorem cubicPolynomialAnnihilator_choose_difference_div
    (n : ℕ) (hn : 4 ≤ n) :
    (n + 2).choose 3 - (n - 1).choose 3 = 1 + 3 * n * (n - 1) / 2 := by
  rw [cubicPolynomialAnnihilator_choose_difference n hn]
  congr 1
  apply Nat.eq_div_of_mul_eq_right (by decide : (2 : ℕ) ≠ 0)
  have htwo := twice_choose_two n
  nlinarith

/-- The actual cubic annihilator has the Coray arithmetic bound dimension. -/
theorem cubicPolynomialDualAnnihilator_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    finrank K (cubicPolynomialDualAnnihilator p hp n hn) =
      1 + 3 * n * (n - 1) / 2 := by
  rw [cubicPolynomialDualAnnihilator_finrank_choose p hp hp0 n hn,
    cubicPolynomialAnnihilator_choose_difference_div n hn]

/-- For n=1,2,3 the relevant full polynomial duals have dimensions 1,4,10.
No fictitious negative-degree multiplication map is introduced. -/
theorem fourVariablePolynomialDual_finrank_small :
    finrank K (Module.Dual K (S 0)) = 1 ∧
      finrank K (Module.Dual K (S 1)) = 4 ∧
        finrank K (Module.Dual K (S 2)) = 10 := by
  simpa only [Subspace.dual_finrank_eq, four_variable_homogeneous_finrank] using
    (by decide : (3 : ℕ).choose 3 = 1 ∧ (4 : ℕ).choose 3 = 4 ∧ (5 : ℕ).choose 3 = 10)

/-- The SAME arithmetic bound gives exactly those full-dual dimensions in
the three positive small degrees. -/
theorem fourVariablePolynomialDual_finrank_of_pos_le_three
    (n : ℕ) (hn : 0 < n) (hsmall : n ≤ 3) :
    finrank K (Module.Dual K (S (n - 1))) =
      1 + 3 * n * (n - 1) / 2 := by
  have hn_cases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl | rfl
  · simpa using (fourVariablePolynomialDual_finrank_small (K := K)).1
  · simpa using (fourVariablePolynomialDual_finrank_small (K := K)).2.1
  · simpa using (fourVariablePolynomialDual_finrank_small (K := K)).2.2

end PfaffianDescent.Coray
