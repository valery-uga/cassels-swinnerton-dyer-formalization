import PfaffianDescent.VoisinCubicCoordinateNormalization
import AllCharacteristics.CubicPolynomialCoordinates

/-! Algebraic coordinate transport without infinitude or
characteristic assumptions. -/

namespace PfaffianDescent.Cubic
open scoped BigOperators
universe u

theorem toMvPolynomial_compLinear_any_characteristic
    {K : Type u} [Field K] {n : ℕ}
    (c : Cubic K n) (M : Matrix (Fin n) (Fin n) K) :
    (c.compLinear M).toMvPolynomial = linearSubstitution M c.toMvPolynomial := by
  calc
    (c.compLinear M).toMvPolynomial =
        ((c.compLinear M).map MvPolynomial.C).eval MvPolynomial.X := by
      simpa only [MvPolynomial.eval₂_eta] using
        eval_toMvPolynomial (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
          (c.compLinear M) MvPolynomial.X
    _ = ((c.map MvPolynomial.C).compLinear (M.map MvPolynomial.C)).eval
        MvPolynomial.X := by rw [compLinear_map]
    _ = (c.map MvPolynomial.C).eval ((M.map MvPolynomial.C).mulVec MvPolynomial.X) :=
      eval_compLinear _ _ _
    _ = linearSubstitution M c.toMvPolynomial := by
      symm
      change MvPolynomial.eval₂ MvPolynomial.C
        ((M.map MvPolynomial.C).mulVec MvPolynomial.X) c.toMvPolynomial = _
      exact eval_toMvPolynomial _ _ _

private theorem eval_polynomial_line
    {R : Type*} [CommRing R] {n : ℕ} (c : Cubic R n) (a b : Fin n → R) :
    (c.map Polynomial.C).eval ((fun i => Polynomial.C (a i)) +
      (Polynomial.X : Polynomial R) • (fun i => Polynomial.C (b i))) =
      Polynomial.C (c.eval a) + Polynomial.C (c.mixed a b) * Polynomial.X +
        Polynomial.C (c.mixed b a) * Polynomial.X ^ 2 +
          Polynomial.C (c.eval b) * Polynomial.X ^ 3 := by
  have h := eval_line (c.map (Polynomial.C : R →+* Polynomial R)) (fun i => Polynomial.C (a i))
    (fun i => Polynomial.C (b i)) 1 (Polynomial.X : Polynomial R)
  simp only [one_smul, one_pow, one_mul, eval_map, mixed_map] at h
  rw [h]
  ring

theorem mixed_compLinear_any_characteristic
    {R : Type*} [CommRing R] {n m : ℕ}
    (c : Cubic R n) (M : Matrix (Fin n) (Fin m) R) (a b : Fin m → R) :
    (c.compLinear M).mixed a b = c.mixed (M.mulVec a) (M.mulVec b) := by
  have h := eval_compLinear (c.map (Polynomial.C : R →+* Polynomial R))
    (M.map (Polynomial.C : R →+* Polynomial R))
    ((fun i => Polynomial.C (a i)) +
      (Polynomial.X : Polynomial R) • (fun i => Polynomial.C (b i)))
  rw [← compLinear_map, Matrix.mulVec_add, Matrix.mulVec_smul] at h
  have ha : (M.map Polynomial.C).mulVec (fun i => Polynomial.C (a i)) =
      fun i => Polynomial.C (M.mulVec a i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, _root_.map_sum,
      _root_.map_mul]
  have hb : (M.map Polynomial.C).mulVec (fun i => Polynomial.C (b i)) =
      fun i => Polynomial.C (M.mulVec b i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, _root_.map_sum,
      _root_.map_mul]
  rw [ha, hb, eval_polynomial_line, eval_polynomial_line] at h
  have hc := congrArg (fun q : Polynomial R => q.coeff 1) h
  simpa [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X] using hc

end PfaffianDescent.Cubic

namespace AllCharacteristics
open PfaffianDescent
universe u

/-- An arbitrary smooth coordinate point admits the affine normalization used
in Kollár's universal-line construction, over its actual ground field. -/
theorem exists_kollar_coordinate_normalization
    {K : Type u} [Field K] (c : Cubic K 4) (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    ∃ M : Matrix (Fin 4) (Fin 4) K, IsUnit M.det ∧
      M.mulVec (kollarBasePoint K) = p ∧
      (c.compLinear M).eval (kollarBasePoint K) = 0 ∧
      (c.compLinear M).mixed (kollarBasePoint K)
        (kollarAffineLineDirection K (fun _ => 0)) ≠ 0 := by
  obtain ⟨d, hd⟩ := exists_tangent_direction_of_isSmoothCubicCoordinatePoint c p hs
  have hp : c.eval p = 0 := by
    have he := hs.2.1
    change MvPolynomial.eval₂ (RingHom.id K) p c.toMvPolynomial = 0 at he
    rw [Cubic.eval_toMvPolynomial] at he
    exact he
  obtain ⟨M, hM, hM0, hM3⟩ := exists_invertible_matrix_mulVec_e0_e3 p d
    (linearIndependent_direction_point_of_mixed_ne_zero c p d hs.1 hp hd)
  have hbase : M.mulVec (kollarBasePoint K) = p := by
    have h : kollarBasePoint K = (Pi.single 0 1 : Fin 4 → K) := by
      funext i
      fin_cases i <;> simp [kollarBasePoint]
    rw [h]
    exact hM0
  have hdir : M.mulVec (kollarAffineLineDirection K (fun _ => 0)) = d := by
    have h : kollarAffineLineDirection K (fun _ => 0) =
        (Pi.single 3 1 : Fin 4 → K) := by
      funext i
      fin_cases i <;> simp [kollarAffineLineDirection]
    rw [h]
    exact hM3
  refine ⟨M, hM, hbase, ?_, ?_⟩
  · rw [Cubic.eval_compLinear, hbase, hp]
  · rw [Cubic.mixed_compLinear_any_characteristic, hbase, hdir]
    exact hd

end AllCharacteristics
