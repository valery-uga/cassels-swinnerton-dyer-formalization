import AllCharacteristics.KollarGenericResidual

/-!
# The generic residual extension over arbitrary ground fields

The previous generic-direction results used polynomial function extensionality
over the ground field.  The coefficient identity below avoids that step and
therefore applies also to finite and imperfect ground fields.
-/

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial

universe u

/-- The coordinate-change identity as an explicit polynomial identity. -/
theorem kollarDistinguishedCoordinatePolynomial_eq_explicit_allFields
    {K : Type u} [Field K] (c : Cubic K 4) :
    kollarDistinguishedCoordinatePolynomial c = kollarExplicitLinePolynomial c := by
  rw [kollarDistinguishedCoordinatePolynomial_eq_lineEvaluation]
  unfold kollarUniversalLineEvaluationPolynomial kollarExplicitLinePolynomial
  simpa only [one_smul] using
    cubic_eval_polynomial_line (kollarProjectiveDirectionCubic c)
      (kollarProjectiveDirectionBase K) (kollarProjectiveLinePolynomialDirection K)

/-- The known base point kills the leading cubic coefficient over every field. -/
theorem kollarProjectiveDirectionBase_eval_eq_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hp : c.eval (kollarBasePoint K) = 0) :
    (kollarProjectiveDirectionCubic c).eval (kollarProjectiveDirectionBase K) = 0 := by
  change (c.map MvPolynomial.C).eval
    (fun i => MvPolynomial.C (kollarBasePoint K i)) = 0
  rw [Cubic.eval_map, hp, map_zero]

/-- The distinguished-coordinate polynomial is a quadratic, explicitly. -/
theorem kollarDistinguishedCoordinatePolynomial_eq_quadratic_allFields
    {K : Type u} [Field K] (c : Cubic K 4)
    (hp : c.eval (kollarBasePoint K) = 0) :
    kollarDistinguishedCoordinatePolynomial c =
      Polynomial.C ((kollarProjectiveDirectionCubic c).eval
        (kollarProjectiveLinePolynomialDirection K)) +
      Polynomial.C ((kollarProjectiveDirectionCubic c).mixed
        (kollarProjectiveLinePolynomialDirection K) (kollarProjectiveDirectionBase K)) *
          Polynomial.X +
      Polynomial.C ((kollarProjectiveDirectionCubic c).mixed
        (kollarProjectiveDirectionBase K) (kollarProjectiveLinePolynomialDirection K)) *
          Polynomial.X ^ 2 := by
  rw [kollarDistinguishedCoordinatePolynomial_eq_explicit_allFields]
  unfold kollarExplicitLinePolynomial
  rw [kollarProjectiveDirectionBase_eval_eq_zero c hp, map_zero, mul_zero, zero_add]
  ring

/-- A selected nonzero first derivative survives in the quadratic coefficient. -/
theorem kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero_allFields
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).coeff 2 ≠ 0 := by
  rw [kollarDistinguishedCoordinatePolynomial_eq_explicit_allFields]
  have hcoeff : (kollarExplicitLinePolynomial c).coeff 2 =
      (kollarProjectiveDirectionCubic c).mixed (kollarProjectiveDirectionBase K)
        (kollarProjectiveLinePolynomialDirection K) := by
    simp [kollarExplicitLinePolynomial, Polynomial.coeff_C_mul]
  rw [hcoeff]
  change (c.map MvPolynomial.C).mixed
    (fun i => MvPolynomial.C (kollarBasePoint K i))
    (kollarProjectiveLinePolynomialDirection K) ≠ 0
  exact kollar_projective_line_secantCoefficient_ne_zero c hsec

/-- No infinitude assumption is needed for the generic degree computation. -/
theorem kollarDistinguishedCoordinatePolynomial_natDegree_eq_two_allFields
    {K : Type u} [Field K] (c : Cubic K 4)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [kollarDistinguishedCoordinatePolynomial_eq_quadratic_allFields c hp]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X,
      show m ≠ 0 by omega, show 1 ≠ m by omega, show m ≠ 2 by omega]
  · exact kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero_allFields c hsec

/-- Gauss's lemma gives the generic distinguished polynomial's irreducibility
even when the original field is finite. -/
theorem kollarDistinguishedCoordinatePolynomial_generic_irreducible_allFields
    {K : Type u} [Field K] (c : Cubic K 4)
    (hirr : Irreducible c.toMvPolynomial)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    Irreducible ((kollarDistinguishedCoordinatePolynomial c).map
      (algebraMap (KollarProjectiveDirectionRing K)
        (FractionRing (KollarProjectiveDirectionRing K)))) := by
  let P := kollarDistinguishedCoordinatePolynomial c
  have hPirr : Irreducible P :=
    hirr.map (MvPolynomial.finSuccEquiv K 3).toRingEquiv
  have hPdegree : P.natDegree ≠ 0 := by
    intro hdegree
    have hcoeff : P.coeff 2 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    exact (kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero_allFields c hsec)
      hcoeff
  exact (hPirr.isPrimitive hPdegree).irreducible_iff_irreducible_map_fraction_map.mp hPirr

/-- Over the generic direction field the actual residual polynomial is the
reciprocal of the distinguished-coordinate quadratic. -/
theorem kollar_generic_distinguished_eq_reverse_residual
    {K : Type u} [Field K] (c : Cubic K 4)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hdir : (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
      (kollarGenericProjectiveLineDirection K) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).map
        (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K))) =
      (Cubic.lineResidualPolynomial
        (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
        (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
          (kollarBasePoint K i))
        (kollarGenericProjectiveLineDirection K)).reverse := by
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let φ : R →+* L := algebraMap R L
  have hc : (kollarProjectiveDirectionCubic c).map φ = c.map (algebraMap K L) := by
    funext i
    exact IsScalarTower.algebraMap_apply K R L (c i)
  have hpmap : (fun i => φ (kollarProjectiveDirectionBase K i)) =
      fun i => algebraMap K L (kollarBasePoint K i) := by
    funext i
    exact IsScalarTower.algebraMap_apply K R L (kollarBasePoint K i)
  rw [kollarDistinguishedCoordinatePolynomial_eq_quadratic_allFields c hp,
    kollar_reverse_lineResidualPolynomial _ _ _ hdir]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  have hceval := Cubic.eval_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveLinePolynomialDirection K)
  have hcmix := Cubic.mixed_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveLinePolynomialDirection K) (kollarProjectiveDirectionBase K)
  have hpmix := Cubic.mixed_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveDirectionBase K) (kollarProjectiveLinePolynomialDirection K)
  have hdmap : (fun i => φ (kollarProjectiveLinePolynomialDirection K i)) =
      kollarGenericProjectiveLineDirection K := rfl
  rw [hc, hdmap] at hceval
  rw [hc, hpmap, hdmap] at hcmix hpmix
  rw [← hceval, ← hcmix, ← hpmix]

/-- The genuine residual quadratic of the generic projective line is
irreducible over the generic-direction field, for every ground field. -/
theorem kollar_generic_projective_line_residual_irreducible_allFields
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (hirr : Irreducible F)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    Irreducible (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K))
        (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) := by
  classical
  let R := MvPolynomial (Fin 3) K
  let L := FractionRing R
  let φ : R →+* L := algebraMap R L
  let cL := c.map (algebraMap K L)
  let pL : Fin 4 → L := fun i => algebraMap K L (kollarBasePoint K i)
  let dL := kollarGenericProjectiveLineDirection K
  let q := Cubic.lineResidualPolynomial cL pL dL
  let P := (kollarDistinguishedCoordinatePolynomial c).map φ
  have hcIrr : Irreducible c.toMvPolynomial := by simpa only [hc] using hirr
  have hPirr : Irreducible P :=
    kollarDistinguishedCoordinatePolynomial_generic_irreducible_allFields c hcIrr hsec
  have hPdegree : P.natDegree = 2 := by
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R L)]
    exact kollarDistinguishedCoordinatePolynomial_natDegree_eq_two_allFields c hp hsec
  have hsecL : cL.mixed pL dL ≠ 0 :=
    kollar_generic_projective_line_secantCoefficient_ne_zero c hsec
  have hdir : cL.eval dL ≠ 0 := by
    have hR := kollarDirectionCubicValuePolynomial_ne_zero_of_irreducible F hF c hc hirr
    intro hzero
    apply hR
    apply IsFractionRing.injective R L
    have he := Cubic.eval_map φ (kollarProjectiveDirectionCubic c)
      (kollarProjectiveLinePolynomialDirection K)
    have hcc : (kollarProjectiveDirectionCubic c).map φ = cL := by
      funext i
      exact IsScalarTower.algebraMap_apply K R L (c i)
    rw [hcc] at he
    change cL.eval dL = φ ((kollarProjectiveDirectionCubic c).eval
      (kollarProjectiveLinePolynomialDirection K)) at he
    rw [hzero] at he
    change φ ((kollarProjectiveDirectionCubic c).eval
      (kollarProjectiveLinePolynomialDirection K)) = φ 0
    simpa only [map_zero] using he.symm
  have hqdeg : q.natDegree = 2 :=
    Cubic.lineResidualPolynomial_natDegree_eq_two cL pL dL hdir
  have hreverse : P = q.reverse :=
    kollar_generic_distinguished_eq_reverse_residual c hp hdir
  by_contra hqirr
  obtain ⟨a, ha⟩ := Cubic.exists_root_of_natDegree_two_of_not_irreducible q hqdeg hqirr
  have ha0 : a ≠ 0 := by
    exact Cubic.lineResidual_root_ne_zero_of_mixed_ne_zero (RingHom.id L)
      cL pL dL hsecL a ha
  letI : Invertible a := invertibleOfNonzero ha0
  have haroot : P.IsRoot (⅟a) := by
    rw [Polynomial.IsRoot.def, hreverse]
    exact (Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id L) a q).mpr ha
  exact hPirr.not_isRoot_of_natDegree_ne_one (by omega) haroot

end AllCharacteristics
