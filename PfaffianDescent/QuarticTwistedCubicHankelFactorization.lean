import PfaffianDescent.QuarticTwistedCubicAffineCoordinates
import PfaffianDescent.QuarticTwistedCubicSymmetricCube

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open scoped MatrixGroups BigOperators

universe u

/-- A primitive Hankel quadruple in a Euclidean domain is a scalar times the
cubic powers of two elements. -/
lemma hankel_factorization
    {R : Type u} [EuclideanDomain R] [GCDMonoid R]
    {f0 f1 f2 f3 : R}
    (hf0 : f0 ≠ 0)
    (h01 : f1 ^ 2 = f0 * f2)
    (h12 : f1 * f2 = f0 * f3)
    (hprimitive : ∀ d : R, d ∣ f0 → d ∣ f1 → d ∣ f2 → d ∣ f3 → IsUnit d) :
    ∃ a b c : R, IsCoprime a b ∧ IsUnit c ∧
      f0 = c * a ^ 3 ∧ f1 = c * a ^ 2 * b ∧
        f2 = c * a * b ^ 2 ∧ f3 = c * b ^ 3 := by
  obtain ⟨a, b, h0, h1, habu⟩ := extract_gcd f0 f1
  have hab : IsCoprime a b := (gcd_isUnit_iff _ _).mp habu
  have hg0 : GCDMonoid.gcd f0 f1 ≠ 0 := by
    intro hg
    rw [h0, hg, zero_mul] at hf0
    exact hf0 rfl
  have ha0 : a ≠ 0 := by
    intro ha
    rw [h0, ha, mul_zero] at hf0
    exact hf0 rfl
  have hgb : GCDMonoid.gcd f0 f1 * b ^ 2 = a * f2 := by
    apply mul_left_cancel₀ hg0
    calc
      GCDMonoid.gcd f0 f1 * (GCDMonoid.gcd f0 f1 * b ^ 2) =
          (GCDMonoid.gcd f0 f1 * b) ^ 2 := by ring
      _ = f1 ^ 2 := congrArg (· ^ 2) h1.symm
      _ = f0 * f2 := h01
      _ = (GCDMonoid.gcd f0 f1 * a) * f2 := congrArg (· * f2) h0
      _ = GCDMonoid.gcd f0 f1 * (a * f2) := by ring
  have hadiv : a ∣ GCDMonoid.gcd f0 f1 := by
    apply (hab.pow_right (n := 2)).dvd_of_dvd_mul_right
    rw [hgb]
    exact dvd_mul_right _ _
  obtain ⟨w, hw⟩ := hadiv
  have hw0 : w ≠ 0 := by
    intro hw0
    rw [hw, hw0, mul_zero] at hg0
    exact hg0 rfl
  have h0' : f0 = w * a ^ 2 := by
    rw [h0, hw]
    ring
  have h1' : f1 = w * a * b := by
    rw [h1, hw]
    ring
  have h2' : f2 = w * b ^ 2 := by
    apply mul_left_cancel₀ ha0
    calc
      a * f2 = GCDMonoid.gcd f0 f1 * b ^ 2 := hgb.symm
      _ = (a * w) * b ^ 2 := by rw [hw]
      _ = a * (w * b ^ 2) := by ring
  have hwb : w * b ^ 3 = a * f3 := by
    apply mul_left_cancel₀ (mul_ne_zero hw0 ha0)
    calc
      (w * a) * (w * b ^ 3) = (w * a * b) * (w * b ^ 2) := by ring
      _ = f1 * f2 := by rw [h1', h2']
      _ = f0 * f3 := h12
      _ = (w * a ^ 2) * f3 := by rw [h0']
      _ = (w * a) * (a * f3) := by ring
  have hawdiv : a ∣ w := by
    apply (hab.pow_right (n := 3)).dvd_of_dvd_mul_right
    rw [hwb]
    exact dvd_mul_right _ _
  obtain ⟨c, hwc⟩ := hawdiv
  have h0'' : f0 = c * a ^ 3 := by
    rw [h0', hwc]
    ring
  have h1'' : f1 = c * a ^ 2 * b := by
    rw [h1', hwc]
    ring
  have h2'' : f2 = c * a * b ^ 2 := by
    rw [h2', hwc]
    ring
  have h3'' : f3 = c * b ^ 3 := by
    apply mul_left_cancel₀ ha0
    calc
      a * f3 = w * b ^ 3 := hwb.symm
      _ = (a * c) * b ^ 3 := by rw [hwc]
      _ = a * (c * b ^ 3) := by ring
  refine ⟨a, b, c, hab, hprimitive c ?_ ?_ ?_ ?_, h0'', h1'', h2'', h3''⟩
  · rw [h0'']
    exact dvd_mul_right _ _
  · rw [h1'']
    simpa [mul_assoc] using dvd_mul_right c (a ^ 2 * b)
  · rw [h2'']
    simpa [mul_assoc] using dvd_mul_right c (a * b ^ 2)
  · rw [h3'']
    exact dvd_mul_right _ _

variable {K : Type u} [Field K]

/-- The affine coordinate polynomials of an invertible matrix preserving the
standard twisted-cubic ideal have the cubic-power factorization forced by
that ideal. -/
theorem affineCubicCoordinate_hankel_factorization
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    ∃ a b c : Polynomial K, IsCoprime a b ∧ IsUnit c ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 0 = c * a ^ 3 ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 1 = c * a ^ 2 * b ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 2 = c * a * b ^ 2 ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 3 = c * b ^ 3 := by
  classical
  letI : GCDMonoid (Polynomial K) :=
    Polynomial.instStrongNormalizedGCDMonoid.toGCDMonoid
  apply hankel_factorization
  · exact affineCubicCoordinate_ne_zero B 0
  · exact (affineCubicCoordinate_hankel_relations (B : Matrix (Fin 4) (Fin 4) K) hB).1
  · exact (affineCubicCoordinate_hankel_relations (B : Matrix (Fin 4) (Fin 4) K) hB).2.1
  · intro d hd0 hd1 hd2 hd3
    apply affineCubicCoordinate_common_dvd_isUnit B d
    intro i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3

/-- In the Hankel factorization of an invertible coordinate change, the two
factors are nonzero affine linear polynomials. -/
theorem affineCubicCoordinate_hankel_linear_factorization
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    ∃ a b c : Polynomial K, IsCoprime a b ∧ IsUnit c ∧ a ≠ 0 ∧ b ≠ 0 ∧
      a.natDegree ≤ 1 ∧ b.natDegree ≤ 1 ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 0 = c * a ^ 3 ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 1 = c * a ^ 2 * b ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 2 = c * a * b ^ 2 ∧
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 3 = c * b ^ 3 := by
  obtain ⟨a, b, c, hab, hc, h0, h1, h2, h3⟩ :=
    affineCubicCoordinate_hankel_factorization B hB
  have hc0 : c ≠ 0 := hc.ne_zero
  have ha0 : a ≠ 0 := by
    intro ha
    have hF0 := affineCubicCoordinate_ne_zero B 0
    rw [h0, ha] at hF0
    simp at hF0
  have hb0 : b ≠ 0 := by
    intro hb
    have hF3 := affineCubicCoordinate_ne_zero B 3
    rw [h3, hb] at hF3
    simp at hF3
  have hadeg : a.natDegree ≤ 1 := by
    have hdeg := affineCubicCoordinate_natDegree_le_three
      (B : Matrix (Fin 4) (Fin 4) K) 0
    rw [h0, Polynomial.natDegree_mul hc0 (pow_ne_zero 3 ha0),
      Polynomial.natDegree_eq_zero_of_isUnit hc, Polynomial.natDegree_pow] at hdeg
    omega
  have hbdeg : b.natDegree ≤ 1 := by
    have hdeg := affineCubicCoordinate_natDegree_le_three
      (B : Matrix (Fin 4) (Fin 4) K) 3
    rw [h3, Polynomial.natDegree_mul hc0 (pow_ne_zero 3 hb0),
      Polynomial.natDegree_eq_zero_of_isUnit hc, Polynomial.natDegree_pow] at hdeg
    omega
  exact ⟨a, b, c, hab, hc, ha0, hb0, hadeg, hbdeg, h0, h1, h2, h3⟩

/-- A polynomial of degree at most one is reconstructed from its constant and
linear coefficients. -/
lemma polynomial_eq_affine_coeff
    (p : Polynomial K) (hp : p.natDegree ≤ 1) :
    p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
  apply Polynomial.eq_X_add_C_of_degree_le_one
  exact Polynomial.natDegree_le_iff_degree_le.mp hp

/-- The cubic symmetric-power matrix of the coefficient matrix of two affine
linear polynomials sends `(1,t,t²,t³)` to their cubic products. -/
lemma affineCubicCoordinate_symmetricCube_affine
    (a b : Polynomial K) (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    let A : Matrix (Fin 2) (Fin 2) K :=
      ![![a.coeff 0, a.coeff 1], ![b.coeff 0, b.coeff 1]]
    ∀ i : Fin 4,
      affineCubicCoordinate (symmetricCubeMatrix A) i = cubicVeronese a b i := by
  dsimp
  have hae := polynomial_eq_affine_coeff a ha
  have hbe := polynomial_eq_affine_coeff b hb
  have hC2 : (Polynomial.C (2 : K) : Polynomial K) = 2 := by
    rw [show (2 : K) = 1 + 1 by norm_num, Polynomial.C_add, Polynomial.C_1]
    norm_num
  have hC3 : (Polynomial.C (3 : K) : Polynomial K) = 3 := by
    rw [show (3 : K) = 1 + 1 + 1 by norm_num, Polynomial.C_add, Polynomial.C_add,
      Polynomial.C_1]
    norm_num
  intro i
  fin_cases i <;>
    rw [hae, hbe] <;>
    simp [affineCubicCoordinate, symmetricCubeMatrix, cubicVeronese,
      Matrix.mulVec, Matrix.map, dotProduct, Fin.sum_univ_succ,
      Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, hC2, hC3] <;> ring

/-- A standard-ideal-preserving invertible ambient matrix is a nonzero scalar
multiple of a cubic symmetric-power matrix. -/
theorem ambient_stabilizer_eq_scalar_symmetricCube
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    ∃ r : K, IsUnit r ∧ ∃ A : Matrix (Fin 2) (Fin 2) K,
      (B : Matrix (Fin 4) (Fin 4) K) = r • symmetricCubeMatrix A := by
  obtain ⟨a, b, c, hab, hc, ha, hb, hadeg, hbdeg, h0, h1, h2, h3⟩ :=
    affineCubicCoordinate_hankel_linear_factorization B hB
  obtain ⟨r, hr, hcr⟩ := Polynomial.isUnit_iff.mp hc
  let A : Matrix (Fin 2) (Fin 2) K :=
    ![![a.coeff 0, a.coeff 1], ![b.coeff 0, b.coeff 1]]
  have hS (i : Fin 4) :
      affineCubicCoordinate (symmetricCubeMatrix A) i = cubicVeronese a b i := by
    simpa only [A] using affineCubicCoordinate_symmetricCube_affine a b hadeg hbdeg i
  have hF (i : Fin 4) :
      affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) i =
        Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) i := by
    fin_cases i
    · calc
        affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 0 = c * a ^ 3 := h0
        _ = Polynomial.C r * a ^ 3 := by rw [hcr]
        _ = Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) 0 := by
          rw [hS 0]
          simp [cubicVeronese]
    · calc
        affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 1 = c * a ^ 2 * b := h1
        _ = Polynomial.C r * a ^ 2 * b := by rw [hcr]
        _ = Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) 1 := by
          rw [hS 1]
          simp [cubicVeronese, mul_assoc]
    · calc
        affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 2 = c * a * b ^ 2 := h2
        _ = Polynomial.C r * a * b ^ 2 := by rw [hcr]
        _ = Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) 2 := by
          rw [hS 2]
          simp [cubicVeronese, mul_assoc]
    · calc
        affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) 3 = c * b ^ 3 := h3
        _ = Polynomial.C r * b ^ 3 := by rw [hcr]
        _ = Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) 3 := by
          rw [hS 3]
          rfl
  refine ⟨r, hr, A, ?_⟩
  ext i j
  calc
    (B : Matrix (Fin 4) (Fin 4) K) i j =
        (affineCubicCoordinate (B : Matrix (Fin 4) (Fin 4) K) i).coeff (j : ℕ) :=
      (affineCubicCoordinate_coeff _ i j).symm
    _ = (Polynomial.C r * affineCubicCoordinate (symmetricCubeMatrix A) i).coeff (j : ℕ) :=
      congrArg (fun p : Polynomial K => p.coeff (j : ℕ)) (hF i)
    _ = r * (affineCubicCoordinate (symmetricCubeMatrix A) i).coeff (j : ℕ) := by
      simp [Polynomial.coeff_C_mul]
    _ = r * symmetricCubeMatrix A i j := by rw [affineCubicCoordinate_coeff]
    _ = (r • symmetricCubeMatrix A) i j := rfl

/-- The cubic symmetric-power matrix of a singular binary matrix cannot be
invertible: a nonzero binary kernel vector gives a nonzero cubic-Veronese
kernel vector. -/
lemma isUnit_det_of_isUnit_symmetricCube
    (A : Matrix (Fin 2) (Fin 2) K) (hS : IsUnit (symmetricCubeMatrix A)) :
    IsUnit A.det := by
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  have hnotA : ¬ IsUnit A := by
    intro hA
    exact (isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det A |>.mp hA)) hdet
  have hnotinj : ¬ Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.not.mpr hnotA
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnotinj
  let v : Fin 2 → K := x - y
  have hvne : v ≠ 0 := by
    simpa only [v] using sub_ne_zero.mpr hne
  have hAv : A.mulVec v = 0 := by
    simp only [v, Matrix.mulVec_sub, hxy, sub_self]
  have hst : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hvne
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hVne : cubicVeronese (v 0) (v 1) ≠ 0 := cubicVeronese_nonzero _ _ hst
  have hvvec : (![v 0, v 1] : Fin 2 → K) = v := by
    funext i
    fin_cases i <;> rfl
  have hSzero : (symmetricCubeMatrix A).mulVec
      (cubicVeronese (v 0) (v 1)) = 0 := by
    rw [cubicVeronese_symmetricCubeMatrix_mulVec, hvvec, hAv]
    simp [cubicVeronese]
  have hSinj : Function.Injective (symmetricCubeMatrix A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hS
  apply hVne
  apply hSinj
  simpa using hSzero

/-- An invertible ambient stabilizer is a nonzero scalar multiple of the
cubic symmetric power of an invertible binary matrix. -/
theorem ambient_stabilizer_eq_scalar_symmetricCube_invertible
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    ∃ r : K, IsUnit r ∧ ∃ A : Matrix (Fin 2) (Fin 2) K,
      IsUnit A.det ∧ (B : Matrix (Fin 4) (Fin 4) K) = r • symmetricCubeMatrix A := by
  obtain ⟨r, hr, A, hBA⟩ := ambient_stabilizer_eq_scalar_symmetricCube B hB
  have hSinj : Function.Injective (symmetricCubeMatrix A).mulVec := by
    have hBinj : Function.Injective (B : Matrix (Fin 4) (Fin 4) K).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr B.isUnit
    intro x y hxy
    apply hBinj
    rw [hBA]
    simp only [Matrix.smul_mulVec]
    rw [hxy]
  have hSunit : IsUnit (symmetricCubeMatrix A) :=
    Matrix.mulVec_injective_iff_isUnit.mp hSinj
  exact ⟨r, hr, A, isUnit_det_of_isUnit_symmetricCube A hSunit, hBA⟩

/-- Every projective ambient transformation preserving the standard twisted
cubic is induced by the cubic symmetric-power action on `PGL₂`. -/
theorem pgl_stabilizer_is_symmetricCube
    (B : GL (Fin 4) K)
    (hB : (standardTwistedCubicIdeal K).map
      (linearSubstitution (B : Matrix (Fin 4) (Fin 4) K)).toRingHom =
        standardTwistedCubicIdeal K) :
    ∃ g : GL (Fin 2) K,
      Matrix.ProjGenLinGroup.mk B =
        symmetricCubePGL (Matrix.ProjGenLinGroup.mk g) := by
  obtain ⟨r, hr, A, hA, hBA⟩ :=
    ambient_stabilizer_eq_scalar_symmetricCube_invertible B hB
  let g : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (isUnit_iff_ne_zero.mp hA)
  refine ⟨g, ?_⟩
  rw [symmetricCubePGL_mk]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨hr.unit⁻¹, ?_⟩
  apply Units.ext
  change (B : Matrix (Fin 4) (Fin 4) K) *
    Matrix.scalar (Fin 4) ((↑(hr.unit⁻¹) : K)) =
      symmetricCubeMatrix A
  rw [hBA]
  simp [← Matrix.mul_smul, ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul, hr.ne_zero]

end PfaffianDescent.QuarticNet
