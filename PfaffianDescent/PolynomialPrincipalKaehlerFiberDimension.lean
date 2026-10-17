import PfaffianDescent.PrincipalPresentationKaehlerFiberQuotient
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/- SOURCE ONLY / UNVERIFIED. The genuine differential fiber of a principal
polynomial presentation has one fewer dimension when its residue gradient
is nonzero. No modeled tangent-space definition occurs. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential Module
open scoped TensorProduct
universe u v w z
variable {k : Type u} {A : Type v} {L : Type w} {σ : Type z} [CommRing k] [CommRing A] [Field L]
  [Fintype σ] [Algebra k A] [Algebra (MvPolynomial σ k) A]
  [IsScalarTower k (MvPolynomial σ k) A] [Algebra A L]

theorem polynomialPrincipal_kaehler_fiber_finrank_add_one
    (h : Function.Surjective (algebraMap (MvPolynomial σ k) A))
    (F : MvPolynomial σ k)
    (hker : RingHom.ker (algebraMap (MvPolynomial σ k) A) = Ideal.span ({F} : Set _))
    (hgrad : ∃ i : σ,
      algebraMap A L (algebraMap (MvPolynomial σ k) A (MvPolynomial.pderiv i F)) ≠ 0) :
    Module.finrank L (L ⊗[A] Ω[A⁄k]) + 1 = Fintype.card σ := by
  classical
  let M := L ⊗[A] (A ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k])
  let w : M := (1 : L) ⊗ₜ[A] ((1 : A) ⊗ₜ[MvPolynomial σ k] D k _ F)
  let b : Basis σ L M := ((mvPolynomialBasis k σ).baseChange A).baseChange L
  letI : Module.Finite L M := Module.Finite.of_basis b
  obtain ⟨i, hi⟩ := hgrad
  have hcoord : b.repr w i =
      algebraMap A L (algebraMap (MvPolynomial σ k) A (MvPolynomial.pderiv i F)) := by
    let b0 := mvPolynomialBasis k σ
    let b1 := b0.baseChange A
    have houter := Basis.baseChange_repr_tmul L b1 (1 : L)
      ((1 : A) ⊗ₜ[MvPolynomial σ k] D k (MvPolynomial σ k) F) i
    have hinner := Basis.baseChange_repr_tmul A b0 (1 : A)
      (D k (MvPolynomial σ k) F) i
    have hpoly := mvPolynomialBasis_repr_apply k σ F i
    calc
      b.repr w i = b1.repr
          ((1 : A) ⊗ₜ[MvPolynomial σ k] D k (MvPolynomial σ k) F) i • (1 : L) :=
        houter
      _ = (b0.repr (D k (MvPolynomial σ k) F) i • (1 : A)) • (1 : L) :=
        congrArg (fun a : A => a • (1 : L)) hinner
      _ = (MvPolynomial.pderiv i F • (1 : A)) • (1 : L) :=
        congrArg (fun r : MvPolynomial σ k => (r • (1 : A)) • (1 : L)) hpoly
      _ = algebraMap A L (algebraMap (MvPolynomial σ k) A
          (MvPolynomial.pderiv i F)) := by
        simp only [Algebra.smul_def, mul_one]
  have hw : w ≠ 0 := by
    intro hw
    apply hi
    rw [← hcoord, hw, map_zero]
    rfl
  let N : Submodule L M := Submodule.span L ({w} : Set M)
  have hN : Module.finrank L N = 1 := _root_.finrank_span_singleton (K := L) (V := M) hw
  have hM : Module.finrank L M = Fintype.card σ := Module.finrank_eq_card_basis b
  have hquot : Module.finrank L (M ⧸ N) + 1 = Fintype.card σ := by
    simpa only [hN, hM] using N.finrank_quotient_add_finrank
  have hEq : Module.finrank L (L ⊗[A] Ω[A⁄k]) = Module.finrank L (M ⧸ N) :=
    (principalPresentationKaehlerFiberQuotientEquiv (k := k) (L := L) h F hker).finrank_eq
  rw [hEq]
  exact hquot

end PfaffianDescent
