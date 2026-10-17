import PfaffianDescent.QuarticTwistedCubicPolynomialStabilizer

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups BigOperators

universe u
variable {K : Type u} [Field K]

/-- The four affine cubic coordinate polynomials induced by an ambient linear
matrix on the parametrization `(1,t,t²,t³)`. -/
noncomputable def affineCubicCoordinate
    (B : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) : Polynomial K :=
  ((B.map (algebraMap K (Polynomial K))).mulVec
    (cubicVeronese (1 : Polynomial K) Polynomial.X)) i

lemma affineCubicCoordinate_eq
    (B : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    affineCubicCoordinate B i =
      ((B.map (algebraMap K (Polynomial K))).mulVec
        (cubicVeronese (1 : Polynomial K) Polynomial.X)) i := rfl

lemma affineCubicCoordinate_coeff
    (B : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (affineCubicCoordinate B i).coeff (j : ℕ) = B i j := by
  fin_cases j <;>
    simp [affineCubicCoordinate, Matrix.mulVec, dotProduct, cubicVeronese,
      Fin.sum_univ_succ]

lemma affineCubicCoordinate_ne_zero
    (B : GL (Fin 4) K) (i : Fin 4) :
    affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) i ≠ 0 := by
  intro hzero
  have hrow (j : Fin 4) : (B : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff (j : ℕ)) hzero
    simpa [affineCubicCoordinate_coeff] using hcoeff
  have hmul : ((B : Matrix (Fin 4) (Fin 4) K) *
      ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) i i = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [hrow j, zero_mul]
  have hinv : (B : Matrix (Fin 4) (Fin 4) K) *
      ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val (mul_inv_cancel B)
  have hdiag := congrFun (congrFun hinv i) i
  rw [hmul] at hdiag
  have h01 : (0 : K) = 1 := by simpa using hdiag
  exact zero_ne_one h01

/-- The four affine cubic coordinate polynomials of an invertible ambient
matrix are primitive as a family. -/
lemma affineCubicCoordinate_common_dvd_isUnit
    (B : GL (Fin 4) K) (d : Polynomial K)
    (hd : ∀ i : Fin 4,
      d ∣ affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) i) :
    IsUnit d := by
  let C : K →+* Polynomial K := algebraMap K (Polynomial K)
  let v : Fin 4 → Polynomial K :=
    cubicVeronese (1 : Polynomial K) Polynomial.X
  let f : Fin 4 → Polynomial K :=
    affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K)
  have hf : f = ((B : Matrix (Fin 4) (Fin 4) K).map C).mulVec v := by
    funext i
    rfl
  have hinv : ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (B : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using
      congrArg Units.val (inv_mul_cancel B)
  have hv : (((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map C).mulVec f = v := by
    rw [hf, Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv]
    simp
  apply isUnit_iff_dvd_one.mpr
  have hv0 : v 0 = 1 := by simp [v, cubicVeronese]
  rw [← hv0, ← hv]
  change d ∣ ∑ i, (((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map C) 0 i * f i
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (hd i) _

/-- Each affine coordinate polynomial has degree at most three. -/
lemma affineCubicCoordinate_natDegree_le_three
    (B : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    (affineCubicCoordinate B i).natDegree ≤ 3 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1' : 1 ≠ n := by omega
  have hn2 : n ≠ 2 := by omega
  have hn3 : n ≠ 3 := by omega
  fin_cases i <;>
    simp [affineCubicCoordinate, Matrix.mulVec, dotProduct, cubicVeronese,
      Fin.sum_univ_succ, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X,
      hn0, hn1', hn2, hn3]

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups

universe u
variable {K : Type u} [Field K]

/-- The affine coordinate polynomials of a standard-ideal-preserving matrix
satisfy the three Hankel identities. -/
theorem affineCubicCoordinate_hankel_relations
    (B : Matrix (Fin 4) (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map (linearSubstitution B).toRingHom =
      standardTwistedCubicIdeal K) :
    affineCubicCoordinate B 1 ^ 2 = affineCubicCoordinate B 0 * affineCubicCoordinate B 2 ∧
      affineCubicCoordinate B 1 * affineCubicCoordinate B 2 =
        affineCubicCoordinate B 0 * affineCubicCoordinate B 3 ∧
      affineCubicCoordinate B 2 ^ 2 = affineCubicCoordinate B 1 * affineCubicCoordinate B 3 := by
  simpa only [affineCubicCoordinate] using
    linearSubstitution_preserving_standardTwistedCubic_polynomial_relations B hB

end PfaffianDescent.QuarticNet
