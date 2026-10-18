import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The generic cubic coordinate vector satisfies
no ground-field linear relation. A graph line whose four coordinates have
descended to the ground field cannot contain such a vector. -/

noncomputable section
namespace AllCharacteristics

open MvPolynomial
open scoped BigOperators

universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- A nonzero cubic equation cannot divide a nonzero linear form. -/
theorem cubic_no_nonzero_linear_relation_in_principal_ideal
    (F ℓ : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (hℓ : ℓ.IsHomogeneous 1) (hdiv : F ∣ ℓ) : ℓ = 0 := by
  by_contra hℓ0
  have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hℓ0
  rw [hF.totalDegree hF0, hℓ.totalDegree hℓ0] at hdeg
  omega

/-- The generic coordinate images in any faithful model of the cubic's
principal coordinate algebra are linearly independent over the ground field. -/
theorem cubic_principal_generic_coordinates_linearIndependent
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (e : MvPolynomial (Fin 4) K →ₐ[K] E)
    (hker : RingHom.ker e.toRingHom = Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))) :
    LinearIndependent K (fun i : Fin 4 => e (MvPolynomial.X i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let ℓ : MvPolynomial (Fin 4) K := ∑ j, a j • MvPolynomial.X j
  have hℓ : ℓ.IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro j _
    simpa only [MvPolynomial.C_mul'] using MvPolynomial.isHomogeneous_C_mul_X (a j) j
  have heval : e ℓ = 0 := by
    simpa only [ℓ, map_sum, map_smul] using ha
  have hdiv : F ∣ ℓ := by
    apply Ideal.mem_span_singleton.mp
    rw [← hker]
    exact heval
  have hzero : ℓ = 0 := cubic_no_nonzero_linear_relation_in_principal_ideal F ℓ hF hF0 hℓ hdiv
  exact Fintype.linearIndependent_iff.mp (MvPolynomial.linearIndependent_X (Fin 4) K) a hzero i

/-- The literal affine-cone generic coordinates have no ground-field linear
relation. Primality is the only algebraic hypothesis beyond the nonzero
homogeneous cubic equation. Smooth cubic irreducibility supplies it. -/
theorem cubic_fractionQuotient_generic_coordinates_linearIndependent
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [(Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime] :
    LinearIndependent K (fun i : Fin 4 =>
      algebraMap (MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)))
        (FractionRing (MvPolynomial (Fin 4) K ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))))
        (Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))) (MvPolynomial.X i))) := by
  let I := Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))
  let A := MvPolynomial (Fin 4) K ⧸ I
  let e : MvPolynomial (Fin 4) K →ₐ[K] FractionRing A :=
    (IsScalarTower.toAlgHom K A (FractionRing A)).comp (Ideal.Quotient.mkₐ K I)
  have hker : RingHom.ker e.toRingHom = I := by
    ext p
    change algebraMap A (FractionRing A) (Ideal.Quotient.mk I p) = 0 ↔ p ∈ I
    constructor
    · intro hp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply IsFractionRing.injective A (FractionRing A)
      simpa only [map_zero] using hp
    · intro hp
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  exact cubic_principal_generic_coordinates_linearIndependent F hF hF0 e hker

/-- A vector with independent homogeneous coordinates cannot lie on a
ground-field graph line. One of the two normal equations already contradicts
linear independence. -/
theorem cubic_generic_coordinates_not_on_ground_graph_line
    (x : Fin 4 → E) (hx : LinearIndependent K x) (a b : K) :
    x 2 ≠ algebraMap K E a * x 0 + algebraMap K E b * x 1 := by
  intro h
  have hrel : ∑ i : Fin 4, (![-a, -b, 1, 0] : Fin 4 → K) i • x i = 0 := by
    simp only [Fin.sum_univ_four]
    change (-a) • x 0 + (-b) • x 1 + (1 : K) • x 2 + (0 : K) • x 3 = 0
    simp only [neg_smul, one_smul, zero_smul, add_zero, Algebra.smul_def,
      map_neg, map_one, map_zero, one_mul, zero_mul, add_zero]
    linear_combination h
  have hcoeff := Fintype.linearIndependent_iff.mp hx _ hrel 2
  simpa using hcoeff

/-- A common nonzero projective rescaling preserves independence of the
homogeneous coordinate vector, so generic normalization is harmless. -/
theorem cubic_generic_coordinates_linearIndependent_rescale
    (x : Fin 4 → E) (hx : LinearIndependent K x) (r : E) (hr : r ≠ 0) :
    LinearIndependent K (fun i => r * x i) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hsum : ∑ j, a j • x j = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hr
    calc
      r * ∑ j, a j • x j = ∑ j, a j • (r * x j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Algebra.smul_def]
        ring
      _ = 0 := ha
  exact Fintype.linearIndependent_iff.mp hx a hsum i

/-- Generic coordinate independence persists in every further field
extension over the same algebraically closed ground field. -/
theorem cubic_generic_coordinates_linearIndependent_map
    {M : Type u} [Field M] [Algebra K M]
    (e : E →ₐ[K] M) (x : Fin 4 → E) (hx : LinearIndependent K x) :
    LinearIndependent K (fun i => e (x i)) := by
  exact hx.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

end AllCharacteristics
