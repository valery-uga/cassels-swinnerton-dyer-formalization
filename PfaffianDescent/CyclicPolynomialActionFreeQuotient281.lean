import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Source-only281. Primitive cyclic monomial equations for a polynomial
module action imply an actual whole kernel ideal quotient with a prescribed
finite basis. No quotient freeness/ideal equality or universal-property
conclusion is assumed. Construction of the universal action is a later cut. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {m n : ℕ}

variable (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
variable (v : Fin n → R)

def polynomialCyclicEvaluation281 : MvPolynomial (Fin m) R →ₗ[R] (Fin n → R) :=
  (LinearMap.applyₗ (R := R) v).comp rho.toLinearMap

lemma polynomialCyclicEvaluation_apply281 (p : MvPolynomial (Fin m) R) :
    polynomialCyclicEvaluation281 rho v p = rho p v := rfl

variable (B : Fin n → (Fin m →₀ ℕ))
variable (hB : ∀ j, rho (monomial (B j) 1) v = Pi.single j 1)

include B hB

lemma polynomialCyclicEvaluation_surjective281 :
    Function.Surjective (polynomialCyclicEvaluation281 rho v) := by
  classical
  intro x
  refine ⟨∑ j : Fin n, x j • monomial (B j) 1, ?_⟩
  calc
    polynomialCyclicEvaluation281 rho v (∑ j : Fin n, x j • monomial (B j) 1) =
        ∑ j : Fin n, x j • polynomialCyclicEvaluation281 rho v (monomial (B j) 1) := by
      simp only [map_sum, map_smul]
    _ = ∑ j : Fin n, x j • Pi.single j 1 := by
      simp only [polynomialCyclicEvaluation_apply281, hB]
    _ = x := by
      funext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]

/-- Cyclicity means that annihilating the unit vector annihilates the whole
free module. The full action kernel therefore equals the vector kernel. -/
lemma polynomialCyclicEvaluation_zero_iff281 (p : MvPolynomial (Fin m) R) :
    polynomialCyclicEvaluation281 rho v p = 0 ↔ rho p = 0 := by
  classical
  constructor
  · intro hp
    change rho p v = 0 at hp
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.zero_apply]
    change rho p (Pi.single j 1) = 0
    rw [← hB j]
    have hc : rho p * rho (monomial (B j) 1) =
        rho (monomial (B j) 1) * rho p := by
      rw [← map_mul, ← map_mul, mul_comm p]
    have hv := congrArg (fun f : Module.End R (Fin n → R) => f v) hc
    change rho p (rho (monomial (B j) 1) v) =
      rho (monomial (B j) 1) (rho p v) at hv
    rw [hv, hp, map_zero]
  · intro hp
    change rho p v = 0
    rw [hp]
    rfl

omit B hB

def cyclicPolynomialQuotientAction281 :
    (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) →ₐ[R]
      Module.End R (Fin n → R) :=
  Ideal.Quotient.liftₐ (RingHom.ker rho.toRingHom) rho
    (fun p hp => RingHom.mem_ker.mp hp)

def cyclicPolynomialQuotientEvaluation281 :
    (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) →ₗ[R] (Fin n → R) :=
  (LinearMap.applyₗ (R := R) v).comp (cyclicPolynomialQuotientAction281 rho).toLinearMap

lemma cyclicPolynomialQuotientEvaluation_mk281 (p : MvPolynomial (Fin m) R) :
    cyclicPolynomialQuotientEvaluation281 rho v
      (Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p) = rho p v := by
  change (Ideal.Quotient.lift (RingHom.ker rho.toRingHom) rho.toRingHom
    (fun p hp => RingHom.mem_ker.mp hp)
      (Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p)) v = rho p v
  rw [Ideal.Quotient.lift_mk]
  rfl

include B hB in
lemma cyclicPolynomialQuotientEvaluation_bijective281 :
    Function.Bijective (cyclicPolynomialQuotientEvaluation281 rho v) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      change cyclicPolynomialQuotientEvaluation281 rho v
        (Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p) = 0 at hq
      rw [cyclicPolynomialQuotientEvaluation_mk281] at hq
      change Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact RingHom.mem_ker.mpr
        ((polynomialCyclicEvaluation_zero_iff281 rho v B hB p).mp hq)
    · exact bot_le
  · intro x
    obtain ⟨p, hp⟩ := polynomialCyclicEvaluation_surjective281 rho v B hB x
    refine ⟨Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p, ?_⟩
    rw [cyclicPolynomialQuotientEvaluation_mk281]
    exact hp

include B hB

def cyclicPolynomialQuotientLinearEquiv281 :
    (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) ≃ₗ[R] (Fin n → R) :=
  LinearEquiv.ofBijective (cyclicPolynomialQuotientEvaluation281 rho v)
    (cyclicPolynomialQuotientEvaluation_bijective281 rho v B hB)

lemma cyclicPolynomialQuotientLinearEquiv_mk281 (p : MvPolynomial (Fin m) R) :
    cyclicPolynomialQuotientLinearEquiv281 rho v B hB
      (Ideal.Quotient.mk (RingHom.ker rho.toRingHom) p) = rho p v :=
  cyclicPolynomialQuotientEvaluation_mk281 rho v p

def cyclicPolynomialQuotientMonomialBasis281 :
    Basis (Fin n) R (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) :=
  (Pi.basisFun R (Fin n)).map (cyclicPolynomialQuotientLinearEquiv281 rho v B hB).symm

lemma cyclicPolynomialQuotientMonomialBasis_apply281 (j : Fin n) :
    cyclicPolynomialQuotientMonomialBasis281 rho v B hB j =
      Ideal.Quotient.mk (RingHom.ker rho.toRingHom) (monomial (B j) 1) := by
  classical
  apply (cyclicPolynomialQuotientLinearEquiv281 rho v B hB).injective
  rw [cyclicPolynomialQuotientLinearEquiv_mk281, hB] <;>
    simp only [cyclicPolynomialQuotientMonomialBasis281, Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply]

include B hB in
lemma cyclicPolynomialQuotient_free_finite281 :
    Module.Free R (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) ∧
      Module.Finite R (MvPolynomial (Fin m) R ⧸ RingHom.ker rho.toRingHom) :=
  ⟨Module.Free.of_basis (cyclicPolynomialQuotientMonomialBasis281 rho v B hB),
    Module.Finite.of_basis (cyclicPolynomialQuotientMonomialBasis281 rho v B hB)⟩

end PfaffianDescent
