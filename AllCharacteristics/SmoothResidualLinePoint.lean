import AllCharacteristics.CubicMultiplicity
import PfaffianDescent.CubicLineResidualTransversality

/-!
# Smooth points from irreducible residual line quadratics

An irreducible residual quadratic of a line through a cubic point gives a
smooth point at its adjoined root in characteristic zero.  The proof records
that the residual root is nonzero and simple, so the original line direction
has nonzero tangent coefficient at that point.
-/

namespace AllCharacteristics

open PfaffianDescent Polynomial

universe u

/-- The point defined by the adjoined root of an irreducible residual line
quadratic is a smooth coordinate point of the cubic in characteristic zero. -/
theorem isSmoothCubicCoordinatePoint_adjoinRoot_lineResidual_of_irreducible_charZero
    {K : Type u} [Field K] [CharZero K]
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hsec : c.mixed p d ≠ 0)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))] :
    IsSmoothCubicCoordinatePoint
      ((c.map (algebraMap K
        (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))).toMvPolynomial)
      ((fun i => algebraMap K
        (AdjoinRoot (Cubic.lineResidualPolynomial c p d)) (p i)) +
        (AdjoinRoot.root (Cubic.lineResidualPolynomial c p d)) •
          (fun i => algebraMap K
            (AdjoinRoot (Cubic.lineResidualPolynomial c p d)) (d i))) := by
  let q := Cubic.lineResidualPolynomial c p d
  have hirr : Irreducible q := Fact.out
  letI : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  let f : K →+* L := algebraMap K L
  let cL : Cubic L 4 := c.map f
  let pL : Fin 4 → L := fun i => f (p i)
  let dL : Fin 4 → L := fun i => f (d i)
  let a : L := AdjoinRoot.root q
  let x : Fin 4 → L := pL + a • dL
  have ha : Polynomial.eval₂ f a q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (AdjoinRoot.root q) q = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hqL : Polynomial.map f q = Cubic.lineResidualPolynomial cL pL dL := by
    exact Cubic.map_lineResidualPolynomial f c p d
  have hroot : Polynomial.eval a (Cubic.lineResidualPolynomial cL pL dL) = 0 := by
    rw [← hqL, Polynomial.eval_map]
    exact ha
  have ha0 : a ≠ 0 := by
    exact Cubic.lineResidual_root_ne_zero_of_mixed_ne_zero f c p d hsec a ha
  have hsimple : Polynomial.eval a
      (Cubic.lineResidualPolynomial cL pL dL).derivative ≠ 0 := by
    have h := hirr.separable.eval₂_derivative_ne_zero f ha
    rw [← hqL, Polynomial.derivative_map, Polynomial.eval_map]
    exact h
  have hx0 : x ≠ 0 := by
    exact Cubic.linePoint_ne_zero_of_eval_zero_eval_ne_zero f c p d hp0 hp hdir a
  have hxeval : cL.eval x = 0 := by
    exact Cubic.eval_linePoint_of_lineResidual_root f c p d hp a ha
  have hmix : cL.mixed x dL ≠ 0 := by
    exact Cubic.mixed_linePoint_direction_ne_zero_of_simple_residual_root
      cL pL dL a ha0 hroot hsimple
  change IsSmoothCubicCoordinatePoint cL.toMvPolynomial x
  exact Cubic.isSmoothCoordinatePoint_of_mixed_ne_zero cL x dL hx0 hxeval hmix

end AllCharacteristics
