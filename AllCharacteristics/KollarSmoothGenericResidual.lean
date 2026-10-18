import AllCharacteristics.KollarGenericResidualAllFields
import AllCharacteristics.KollarCharacteristicTwoActualResidual
import AllCharacteristics.ResidualSeparabilityAllCharacteristics

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial

universe u

/-- The actual residual quadratic on the generic line through the normalized
base point, over the three-variable generic direction field. -/
noncomputable def kollarGenericResidualPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    Polynomial (FractionRing (MvPolynomial (Fin 3) K)) :=
  Cubic.lineResidualPolynomial
    (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
    (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
      (kollarBasePoint K i))
    (kollarGenericProjectiveLineDirection K)

/-- Actual smoothness makes the generic residual quadratic irreducible over
any ground field, including finite and imperfect fields. -/
theorem kollarGenericResidualPolynomial_irreducible_of_smooth
    {K : Type u} [Field K] (c : Cubic K 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    Irreducible (kollarGenericResidualPolynomial c) := by
  have hc0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hprime : (Ideal.span ({c.toMvPolynomial} :
      Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic c.toMvPolynomial hhom hc0
  have hirr : Irreducible c.toMvPolynomial :=
    ((Ideal.span_singleton_prime hc0).mp hprime).irreducible
  exact kollar_generic_projective_line_residual_irreducible_allFields
    c.toMvPolynomial hhom c rfl hirr hp hsec

/-- Smoothness also makes the actual generic residual separable.  The
characteristic-two case uses the smooth partial-derivative argument; all other
characteristics use the explicit quadratic derivative coefficients. -/
theorem kollarGenericResidualPolynomial_separable_of_smooth
    {K : Type u} [Field K] (c : Cubic K 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (kollarGenericResidualPolynomial c).Separable := by
  classical
  by_cases htwo : (2 : K) = 0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 2)).mpr htwo
    exact kollar_generic_projective_line_residual_separable_charTwo c hhom
      (kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec) hp hsec
  · let L := FractionRing (MvPolynomial (Fin 3) K)
    let cL := c.map (algebraMap K L)
    let pL : Fin 4 → L := fun i => algebraMap K L (kollarBasePoint K i)
    let dL := kollarGenericProjectiveLineDirection K
    have hdir : cL.eval dL ≠ 0 :=
      kollar_generic_projective_line_eval_ne_zero_of_smooth c.toMvPolynomial hhom c rfl hsec
    have hirr : Irreducible (Cubic.lineResidualPolynomial cL pL dL) :=
      kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec
    apply (Cubic.lineResidualPolynomial_separable_iff cL pL dL hdir hirr).mpr
    right
    intro htwoL
    apply htwo
    apply (algebraMap K L).injective
    simpa only [map_ofNat, map_zero] using htwoL

/-- The residual extension has exact degree two, with no cardinality or
characteristic restriction on the original field. -/
theorem kollarGenericResidualPolynomial_natDegree_of_smooth
    {K : Type u} [Field K] (c : Cubic K 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (kollarGenericResidualPolynomial c).natDegree = 2 := by
  apply Cubic.lineResidualPolynomial_natDegree_eq_two
  exact kollar_generic_projective_line_eval_ne_zero_of_smooth
    c.toMvPolynomial hhom c rfl hsec

end AllCharacteristics
