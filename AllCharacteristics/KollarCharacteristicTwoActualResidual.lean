import AllCharacteristics.KollarCharacteristicTwoResidual

/-! Separability of the actual generic residual quadratic,
over every characteristic-two field, from actual smoothness. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry MvPolynomial Polynomial HomogeneousProjective PfaffianDescent
universe u

theorem kollar_generic_projective_line_reverseMixed_ne_zero_charTwo
    {K : Type u} [Field K] [CharP K 2]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c.toMvPolynomial ≠ 0)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).mixed
      (kollarGenericProjectiveLineDirection K)
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
        (kollarBasePoint K i)) ≠ 0 := by
  let R := KollarProjectiveDirectionRing K
  let L := FractionRing R
  let φ : R →+* L := algebraMap R L
  have hφ : Function.Injective φ := IsFractionRing.injective R L
  have hcoeff : (kollarDistinguishedCoordinatePolynomial c).coeff 1 =
      (kollarProjectiveDirectionCubic c).mixed
        (kollarProjectiveLinePolynomialDirection K)
        (kollarProjectiveDirectionBase K) := by
    rw [kollarDistinguishedCoordinatePolynomial_eq_quadratic_allFields c hp]
    simp [Polynomial.coeff_C_mul]
  have hmixed : (kollarProjectiveDirectionCubic c).mixed
      (kollarProjectiveLinePolynomialDirection K)
      (kollarProjectiveDirectionBase K) ≠ 0 := by
    rw [← hcoeff]
    exact kollarDistinguishedCoordinatePolynomial_coeff_one_ne_zero_charTwo
      c hhom hc0 hp hsec
  have hc : (kollarProjectiveDirectionCubic c).map φ =
      c.map (algebraMap K L) := by
    funext i
    exact IsScalarTower.algebraMap_apply K R L (c i)
  have hpmap : (fun i => φ (kollarProjectiveDirectionBase K i)) =
      fun i => algebraMap K L (kollarBasePoint K i) := by
    funext i
    exact IsScalarTower.algebraMap_apply K R L (kollarBasePoint K i)
  have hdmap : (fun i => φ (kollarProjectiveLinePolynomialDirection K i)) =
      kollarGenericProjectiveLineDirection K := rfl
  have hmap := Cubic.mixed_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveLinePolynomialDirection K) (kollarProjectiveDirectionBase K)
  rw [hc, hpmap, hdmap] at hmap
  rw [hmap]
  intro hzero
  exact hmixed (hφ (by simpa only [map_zero] using hzero))

/-- An explicit constant-derivative Bezout identity proves separability in
characteristic two, without a perfectness or irreducibility hypothesis. -/
theorem quadratic_separable_of_linearCoeff_ne_zero_charTwo
    {L : Type*} [Field L] [CharP L 2] (q : L[X])
    (hdeg : q.natDegree ≤ 2) (hlinear : q.coeff 1 ≠ 0) :
    q.Separable := by
  have hderiv : q.derivative = Polynomial.C (q.coeff 1) :=
    quadratic_derivative_eq_C_linearCoeff_of_two_eq_zero q hdeg
      (CharP.cast_eq_zero L 2)
  apply (Polynomial.separable_def' q).mpr
  refine ⟨0, Polynomial.C (q.coeff 1)⁻¹, ?_⟩
  rw [hderiv]
  simp [← Polynomial.C_mul, hlinear]

/-- The actual generic line residual is separable over any characteristic-two
field. The hypotheses are only a normalized smooth cubic and its selected
nonzero tangent coefficient. -/
theorem kollar_generic_projective_line_residual_separable_charTwo
    {K : Type u} [Field K] [CharP K 2]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c.toMvPolynomial ≠ 0)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
        (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)).Separable := by
  let L := FractionRing (MvPolynomial (Fin 3) K)
  let cL := c.map (algebraMap K L)
  let pL : Fin 4 → L := fun i => algebraMap K L (kollarBasePoint K i)
  let dL := kollarGenericProjectiveLineDirection K
  let q := Cubic.lineResidualPolynomial cL pL dL
  have hdegree : q.natDegree ≤ 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : 1 ≠ m := by omega
    have hm2 : m ≠ 2 := by omega
    simp [q, Cubic.lineResidualPolynomial, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C, hm0, hm1, hm2]
  have hlinear : q.coeff 1 ≠ 0 := by
    simpa [q, Cubic.lineResidualPolynomial, Polynomial.coeff_C_mul] using
      kollar_generic_projective_line_reverseMixed_ne_zero_charTwo
        c hhom hc0 hp hsec
  exact quadratic_separable_of_linearCoeff_ne_zero_charTwo q hdegree hlinear

end AllCharacteristics
