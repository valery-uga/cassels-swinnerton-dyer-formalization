import PfaffianDescent.CorayAlgClosedNonvanishingSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Actual tensor domain for arbitrary extensions of an algebraically closed field

Nonzero tensors have nonzero actual basis coefficients. Constructed finite-type
specialization preserves the product of two such coefficients, so it sends
both tensors to nonzero elements of the actual extension FIELD. This rules out
zero divisors, including for transcendental extensions. No tensor-domain,
prime-extension or GI certificate is supplied. SOURCE ONLY / UNVERIFIED.
-/
noncomputable section
namespace PfaffianDescent.Coray
open Module
open scoped TensorProduct
universe u v w
variable {Ω : Type u} {A : Type v} {T : Type w}
variable [Field Ω] [CommRing A] [Algebra Ω A] [Field T] [Algebra Ω T]

/-- The literal specialization of the A factor of the actual algebra tensor
product, followed by the native tensor unit isomorphism. -/
def algebraTensorCoefficientSpecialization (φ : A →ₐ[Ω] Ω) : A ⊗[Ω] T →ₐ[Ω] T :=
  (Algebra.TensorProduct.lid Ω T).toAlgHom.comp
    (Algebra.TensorProduct.map φ (AlgHom.id Ω T))

/-- Actual basis coordinates commute with the literal tensor specialization.
This is proved on tensor generators, not assumed as a naturality certificate. -/
theorem algebraTensorCoefficientSpecialization_basis_coordinate
    {ι : Type*} [DecidableEq ι] (φ : A →ₐ[Ω] Ω) (b : Basis ι Ω T) (x : A ⊗[Ω] T) (i : ι) :
    b.repr (algebraTensorCoefficientSpecialization φ x) i =
      φ (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
      simp [algebraTensorCoefficientSpecialization,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul, smul_eq_mul, mul_comm]
  | add x y hx hy => simp [map_add, Finsupp.add_apply, hx, hy]

/-- A finite-type domain over an algebraically closed field remains an ACTUAL
DOMAIN after tensoring with ANY extension field, including transcendental
ones. No Algebra.IsAlgebraic Ω T or desired domain/GI premise occurs. -/
theorem algClosedFiniteTypeDomain_tensorProduct_isDomain
    [IsAlgClosed Ω] [IsDomain A] [Algebra.FiniteType Ω A] : IsDomain (A ⊗[Ω] T) := by
  classical
  let b := Module.Free.chooseBasis Ω T
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  letI : Nontrivial (A ⊗[Ω] T) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain Ω A T
      (RingHom.injective _) (RingHom.injective _)
  letI : NoZeroDivisors (A ⊗[Ω] T) := ⟨by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    by_cases hy : y = 0
    · exact Or.inr hy
    have hx' : e x ≠ 0 := by
      intro h
      apply hx
      apply e.injective
      simpa using h
    have hy' : e y ≠ 0 := by
      intro h
      apply hy
      apply e.injective
      simpa using h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hx'
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hy'
    have hi' : e x i ≠ 0 := by simpa only [Finsupp.zero_apply] using hi
    have hj' : e y j ≠ 0 := by simpa only [Finsupp.zero_apply] using hj
    obtain ⟨φ, hφ⟩ := finiteTypeDomain_exists_algHom_nonzero (Ω := Ω)
      ((e x i) * (e y j)) (mul_ne_zero hi' hj')
    have hφi : φ (e x i) ≠ 0 := by
      intro h
      apply hφ
      simp only [map_mul, h, zero_mul]
    have hφj : φ (e y j) ≠ 0 := by
      intro h
      apply hφ
      simp only [map_mul, h, mul_zero]
    let ψ := algebraTensorCoefficientSpecialization (T := T) φ
    have hxψ : ψ x ≠ 0 := by
      intro h
      apply hφi
      rw [← algebraTensorCoefficientSpecialization_basis_coordinate φ b x i]
      change b.repr (ψ x) i = 0
      rw [h]
      simp
    have hyψ : ψ y ≠ 0 := by
      intro h
      apply hφj
      rw [← algebraTensorCoefficientSpecialization_basis_coordinate φ b y j]
      change b.repr (ψ y) j = 0
      rw [h]
      simp
    have hψxy : ψ x * ψ y = 0 := by rw [← map_mul, hxy, map_zero]
    exact False.elim ((mul_ne_zero hxψ hyψ) hψxy)⟩
  exact NoZeroDivisors.to_isDomain _

end PfaffianDescent.Coray
