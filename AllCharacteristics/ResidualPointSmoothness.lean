import AllCharacteristics.TangentHyperplaneGeneric
import PfaffianDescent.CubicLineResidualTransversality

namespace AllCharacteristics

open PfaffianDescent MvPolynomial Polynomial

universe u

/-- A nonzero tangent pairing at a cubic point already certifies its complete
smooth projective-coordinate condition, including nonzero coordinates. -/
theorem isSmoothCubicCoordinatePoint_of_mixed_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hmix : c.mixed p d ≠ 0) :
    IsSmoothCubicCoordinatePoint c.toMvPolynomial p := by
  have hp0 : p ≠ 0 := by
    intro hzero
    apply hmix
    simp [hzero, PfaffianDescent.Cubic.mixed]
  have hgrad : ∃ i : Fin 4,
      (MvPolynomial.pderiv i c.toMvPolynomial).eval p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hmix
    rw [Cubic.mixed_eq_sum_pderiv_eval]
    simp only [h, mul_zero, Finset.sum_const_zero]
  refine ⟨hp0, ?_, hgrad⟩
  change MvPolynomial.eval₂ (RingHom.id K) p c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact hp

/-- Every nonzero simple residual root on a line through a cubic point gives
a smooth projective-coordinate point, after arbitrary coefficient extension. -/
theorem isSmoothCubicCoordinatePoint_of_simple_lineResidual_root
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (b : L)
    (hroot : Polynomial.eval₂ f b (Cubic.lineResidualPolynomial c p d) = 0)
    (hsimple : Polynomial.eval₂ f b
      (Cubic.lineResidualPolynomial c p d).derivative ≠ 0) :
    IsSmoothCubicCoordinatePoint (c.map f).toMvPolynomial
      ((fun i => f (p i)) + b • (fun i => f (d i))) := by
  let cL := c.map f
  let pL : Fin 4 → L := fun i => f (p i)
  let dL : Fin 4 → L := fun i => f (d i)
  have hqL : Polynomial.map f (Cubic.lineResidualPolynomial c p d) =
      Cubic.lineResidualPolynomial cL pL dL :=
    Cubic.map_lineResidualPolynomial f c p d
  apply isSmoothCubicCoordinatePoint_of_mixed_ne_zero cL (pL + b • dL) dL
  · exact Cubic.eval_linePoint_of_lineResidual_root f c p d hp b hroot
  · apply Cubic.mixed_linePoint_direction_ne_zero_of_simple_residual_root
    · exact Cubic.lineResidual_root_ne_zero_of_mixed_ne_zero f c p d hsec b hroot
    · rw [← hqL, Polynomial.eval_map]
      exact hroot
    · rw [← hqL, Polynomial.derivative_map, Polynomial.eval_map]
      exact hsimple

/-- For a separable residual polynomial, smoothness follows directly from
the given root and the nonzero secant coefficient at the original point. -/
theorem isSmoothCubicCoordinatePoint_of_separable_lineResidual_root
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hsep : (Cubic.lineResidualPolynomial c p d).Separable)
    (b : L)
    (hroot : Polynomial.eval₂ f b (Cubic.lineResidualPolynomial c p d) = 0) :
    IsSmoothCubicCoordinatePoint (c.map f).toMvPolynomial
      ((fun i => f (p i)) + b • (fun i => f (d i))) :=
  isSmoothCubicCoordinatePoint_of_simple_lineResidual_root f c p d hp hsec b
    hroot (hsep.eval₂_derivative_ne_zero f hroot)

end AllCharacteristics
