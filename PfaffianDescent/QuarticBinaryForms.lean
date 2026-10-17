import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases

/-!
# Homogeneous binary forms used by the matching-line branch of Section 4
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial

section
variable {K : Type*} [Field K]

/-- The exponent of `x₀ⁿ⁻ⁱx₁ⁱ`. -/
noncomputable def binaryExponent (n : ℕ) (i : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (n - i.val) + Finsupp.single 1 i.val

theorem binaryExponent_injective (n : ℕ) : Function.Injective (binaryExponent n) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  simpa [binaryExponent] using hh

theorem binaryExponent_degree (n : ℕ) (i : Fin (n + 1)) :
    (binaryExponent n i).degree = n := by
  rw [binaryExponent, Finsupp.degree_eq_sum]
  simp [Fin.sum_univ_two]
  omega

private theorem binaryExponent_complete (n : ℕ) (d : Fin 2 →₀ ℕ) (hd : d.degree = n) :
    ∃ i, binaryExponent n i = d := by
  have hsum : d 0 + d 1 = n := by
    change d.sum (fun _ m => m) = n at hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
    simpa [Fin.sum_univ_two] using hd
  refine ⟨⟨d 1, by omega⟩, ?_⟩
  ext i
  fin_cases i
  · simp [binaryExponent]
    omega
  · simp [binaryExponent]

noncomputable def binaryForm (n : ℕ) (q : Fin (n + 1) → K) : MvPolynomial (Fin 2) K :=
  ∑ i, monomial (binaryExponent n i) (q i)

theorem binaryForm_coeff (n : ℕ) (q : Fin (n + 1) → K) (i : Fin (n + 1)) :
    coeff (binaryExponent n i) (binaryForm n q) = q i := by
  simp [binaryForm, coeff_sum, coeff_monomial, (binaryExponent_injective n).eq_iff]

theorem binaryForm_homogeneous (n : ℕ) (q : Fin (n + 1) → K) :
    (binaryForm n q).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_monomial _ (binaryExponent_degree n i))

theorem binaryForm_exhaustive (n : ℕ) (F : MvPolynomial (Fin 2) K) (hF : F.IsHomogeneous n) :
    binaryForm n (fun i => coeff (binaryExponent n i) F) = F := by
  ext d
  by_cases hd : d.degree = n
  · obtain ⟨i, rfl⟩ := binaryExponent_complete n d hd
    exact binaryForm_coeff _ _ _
  · have h1 := hF.coeff_eq_zero hd
    have h2 := (binaryForm_homogeneous n (fun i => coeff (binaryExponent n i) F)).coeff_eq_zero hd
    rw [h1, h2]

/-- The four-coefficient expansion of every homogeneous binary cubic. -/
theorem binary_cubic_expansion (F : MvPolynomial (Fin 2) K) (hF : F.IsHomogeneous 3) :
    ∃ a b c d : K,
      F = C a * X 0 ^ 3 + C b * X 0 ^ 2 * X 1 +
        C c * X 0 * X 1 ^ 2 + C d * X 1 ^ 3 := by
  let q := fun i => coeff (binaryExponent 3 i) F
  refine ⟨q 0, q 1, q 2, q 3, ?_⟩
  rw [← binaryForm_exhaustive 3 F hF]
  simp [binaryForm, binaryExponent, Fin.sum_univ_four, monomial_eq,
    Finsupp.prod_fintype, Fin.prod_univ_two, Finsupp.single_apply, q]
  ring

end
end QuarticNet
end PfaffianDescent
