import PfaffianDescent.Trivector
import PfaffianDescent.SquareOperator
import PfaffianDescent.IsotropicPoint
import PfaffianDescent.PfaffianCubic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.CharP.Algebra

namespace PfaffianDescent
open Polynomial
open scoped BigOperators

section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- A stable common contraction-kernel vector gives a point when its discriminant is a square. -/
theorem pfaffian_point_of_stable_square (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i)) (p : Vec K 20)
    (hc : ∀ i : Fin 3, contract3 (A i.castSucc) p = 0)
    (r : K) (hr : r ≠ 0) (hsq : r^2 = trivectorDiscriminant p) : HasPfaffianPoint A := by
  let H := hitchin p
  let f := H.transpose.mulVecLin
  let B : Fin 3 → LinearMap.BilinForm K (Vec K 6) :=
    fun i => Matrix.toBilin' (A i.castSucc)
  have hH : H.transpose * H.transpose = r^2 • (1 : Mat K 6) := by
    have hh := congrArg Matrix.transpose (hitchin_square p)
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one, ← hsq] using hh
  have hff : ∀ v, f (f v) = r^2 • v := by
    intro v
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hH,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcomp : ∀ i v w, B i (f v) w + B i v (f w) = 0 := by
    intro i v w
    have hh := congrArg (fun M : Mat K 6 => v ⬝ᵥ M.mulVec w)
      (hitchin_compatible (A i.castSucc) (hA i.castSucc) p (hc i))
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add,
      Matrix.zero_mulVec, dotProduct_zero] at hh
    have ht : v ⬝ᵥ H.mulVec ((A i.castSucc).mulVec w) =
        H.transpose.mulVec v ⬝ᵥ (A i.castSucc).mulVec w := by
      simpa only [Matrix.transpose_transpose] using
        (Matrix.dotProduct_transpose_mulVec H.transpose v ((A i.castSucc).mulVec w)).trans
          (dotProduct_comm _ _)
    simp only [B, Matrix.toBilin'_apply', f, Matrix.mulVecLin_apply]
    rw [← ht, add_comm]
    exact hh
  obtain ⟨W, hW, hWB⟩ := common_isotropic_of_square
    (show Module.finrank K (Vec K 6) = 6 by simp [Vec]) B f r
    (mul_ne_zero (NeZero.ne _) hr) hff hcomp
  apply pfaffian_point_of_isotropic_three_space A hA W hW
  intro i v w
  simpa only [B, Matrix.toBilin'_apply'] using hWB i v w

/-- Alternation is preserved by extension of scalars. -/
theorem isAlternating_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Mat R 6) (hA : IsAlternating A) : IsAlternating (A.map f) := by
  constructor
  · intro i
    change f (A i i) = 0
    rw [hA.1 i, map_zero]
  · intro i j
    change f (A j i) = -f (A i j)
    rw [hA.2 i j, map_neg]

/-- A stable vector in the simultaneous contraction kernel suffices over the ground field.
The square root is adjoined only inside the proof, and quadratic secant descent removes it. -/
theorem pfaffian_point_of_stable_kernel (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i)) (p : Vec K 20)
    (hc : ∀ i : Fin 3, contract3 (A i.castSucc) p = 0)
    (hp : trivectorDiscriminant p ≠ 0) : HasPfaffianPoint A := by
  classical
  by_cases hs : ∃ r : K, r^2 = trivectorDiscriminant p
  · obtain ⟨r, hr⟩ := hs
    have hr0 : r ≠ 0 := by
      intro hz
      apply hp
      rw [← hr, hz, zero_pow (by decide)]
    exact pfaffian_point_of_stable_square A hA p hc r hr0 hr
  · let g : K[X] := Polynomial.X^2 - Polynomial.C (trivectorDiscriminant p)
    have hg : Irreducible g := by
      apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
      intro r hr
      exact hs ⟨r, hr⟩
    let : Fact (Irreducible g) := ⟨hg⟩
    let L := AdjoinRoot g
    let f := algebraMap K L
    let : NeZero (2 : L) := ⟨by
      change f (2 : K) ≠ 0
      exact (map_ne_zero_iff f (algebraMap K L).injective).mpr (NeZero.ne _)⟩
    let : FiniteDimensional K L := Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
    have hdim : Module.finrank K L = 2 := by
      rw [(AdjoinRoot.powerBasis hg.ne_zero).finrank]
      simp only [AdjoinRoot.powerBasis_dim, g, Polynomial.natDegree_X_pow_sub_C]
    let r : L := AdjoinRoot.root g
    have hr : r^2 = f (trivectorDiscriminant p) := by
      have hh := AdjoinRoot.eval₂_root g
      simp only [g, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero] at hh
      exact hh
    have hr0 : r ≠ 0 := by
      intro hz
      have hh : f (trivectorDiscriminant p) = 0 := by rw [← hr, hz, zero_pow (by decide)]
      exact hp ((map_eq_zero f).mp hh)
    have hcL : ∀ i : Fin 3, contract3 ((A i.castSucc).map f) (fun j => f (p j)) = 0 := by
      intro i
      rw [contract3_map, hc i]
      funext j
      exact map_zero f
    have hpoint := pfaffian_point_of_stable_square (fun i => (A i).map f)
      (fun i => isAlternating_map f (A i) (hA i)) (fun j => f (p j)) hcL r hr0
      (hr.trans (trivectorDiscriminant_map f p).symm)
    exact pfaffian_quadratic_secant hdim A hpoint

end
end PfaffianDescent
