import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum

namespace PfaffianDescent
open Module

section
variable {K : Type*} [Field K]

/-- The monomial count gives the dimension of the actual homogeneous polynomial submodule. -/
theorem homogeneous_polynomial_finrank (n d : ℕ) :
    finrank K (MvPolynomial.homogeneousSubmodule (Fin n) K d) = (n + d - 1).choose d := by
  classical
  let S : Set (Fin n →₀ ℕ) := {a | a.degree = d}
  have E : Sym (Fin n) d ≃ S := Sym.equivNatSum (Fin n) d
  letI : Fintype S := Fintype.ofEquiv _ E
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  calc
    _ = Fintype.card S := finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K S)
    _ = Fintype.card (Sym (Fin n) d) := (Fintype.card_congr E).symm
    _ = (n + d - 1).choose d := by simp only [Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The six-dimensional space of plane conic equations. -/
theorem plane_conic_finrank : finrank K (MvPolynomial.homogeneousSubmodule (Fin 3) K 2) = 6 := by
  rw [homogeneous_polynomial_finrank]
  decide

/-- The degree-d piece of the polynomial ring on projective three-space. -/
theorem four_variable_homogeneous_finrank (d : ℕ) :
    finrank K (MvPolynomial.homogeneousSubmodule (Fin 4) K d) = (d + 3).choose 3 := by
  rw [homogeneous_polynomial_finrank]
  have h : 4 + d - 1 = d + 3 := by omega
  rw [h]
  exact Nat.choose_symm_add

end
end PfaffianDescent
