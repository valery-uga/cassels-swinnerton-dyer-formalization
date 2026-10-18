import AllCharacteristics.GenericDistinguishedRootKernel
import AllCharacteristics.HomogeneousKernelLinearIndependence
import AllCharacteristics.CubicGenericLineExclusion
import AllCharacteristics.SmoothCubicGenericNoContainedLine
import AllCharacteristics.KollarGenericResidualAllFields

/-! Genericity of an actual residual center over the
smaller constant ground field K, which may be an algebraic closure of the
original field. The parameter variables remain transcendental over K.
This theorem must NOT be applied with the whole splitting field as K. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial
universe u

/-- The actual generic line point is a nonzero common rescaling of the
distinguished-root cone coordinates at the reciprocal parameter. -/
theorem kollar_linePoint_eq_scaled_distinguishedRoot_coordinates
    {K E : Type u} [Field K] [Field E]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) E]
    (r : E) (hr : r ≠ 0) :
    (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))) +
      r • (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (kollarGenericProjectiveLineDirection K i)) =
      fun i => r * distinguishedRootConeEvaluation (K := K) r⁻¹ (MvPolynomial.X i) := by
  funext i
  fin_cases i <;>
    simp [kollarBasePoint, kollarGenericProjectiveLineDirection,
      kollarProjectiveLinePolynomialDirection_eq_standard,
      distinguishedRootConeEvaluation_X_zero, hr]
  · exact (distinguishedRootConeEvaluation_X_succ (K := K) r⁻¹ (0 : Fin 3)).symm
  · exact (distinguishedRootConeEvaluation_X_succ (K := K) r⁻¹ (1 : Fin 3)).symm
  · exact (distinguishedRootConeEvaluation_X_succ (K := K) r⁻¹ (2 : Fin 3)).symm

/-- A nonzero actual residual root is reciprocal to a distinguished cubic
coordinate root. This is an explicit polynomial identity, valid over every
further extension of the generic direction field. -/
theorem kollar_distinguished_eval_inv_eq_zero_of_residual_root
    {K E : Type u} [Field K] [Field E]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) E]
    (c : Cubic K 4) (hp : c.eval (kollarBasePoint K) = 0)
    (hdir : (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
      (kollarGenericProjectiveLineDirection K) ≠ 0)
    (r : E) (hr : r ≠ 0)
    (hroot : Polynomial.aeval r (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) = 0) :
    Polynomial.aeval r⁻¹ ((kollarDistinguishedCoordinatePolynomial c).map
      (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)))) = 0 := by
  letI : Invertible r := invertibleOfNonzero hr
  rw [kollar_generic_distinguished_eq_reverse_residual c hp hdir]
  change Polynomial.eval₂ (algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E)
    r⁻¹ _ = 0
  simpa only [invOf_eq_inv] using
    (Polynomial.eval₂_reverse_eq_zero_iff
      (algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E) r _).mpr hroot

set_option backward.isDefEq.respectTransparency false in
/-- An actual residual center has coordinates linearly independent over the
constant ground field. The larger field E may already be algebraically closed. -/
theorem kollar_residual_center_linearIndependent
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) E]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 3) K)) E]
    (c : Cubic K 4) (hirr : Irreducible c.toMvPolynomial)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    (hdir : (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)))).eval
      (kollarGenericProjectiveLineDirection K) ≠ 0)
    (r : E) (hr : r ≠ 0)
    (hroot : Polynomial.aeval r (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) = 0) :
    LinearIndependent K
      ((fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
          (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))) +
        r • (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
          (kollarGenericProjectiveLineDirection K i))) := by
  let R := MvPolynomial (Fin 3) K
  let Q := FractionRing R
  let e := distinguishedRootConeEvaluation (K := K) r⁻¹
  have hbase : e.comp MvPolynomial.C = algebraMap K E := by
    ext x
    simp [e, distinguishedRootConeEvaluation, MvPolynomial.finSuccEquiv_apply]
    change algebraMap Q E (algebraMap R Q (algebraMap K R x)) = algebraMap K E x
    rw [← IsScalarTower.algebraMap_apply K R Q, ← IsScalarTower.algebraMap_apply K Q E]
  have hdegree : (MvPolynomial.finSuccEquiv K 3 c.toMvPolynomial).natDegree ≠ 0 := by
    change (kollarDistinguishedCoordinatePolynomial c).natDegree ≠ 0
    rw [kollarDistinguishedCoordinatePolynomial_natDegree_eq_two_allFields c hp hsec]
    decide
  have hrootInv := kollar_distinguished_eval_inv_eq_zero_of_residual_root
    c hp hdir r hr hroot
  have hker : RingHom.ker e = Ideal.span ({c.toMvPolynomial} : Set (MvPolynomial (Fin 4) K)) :=
    distinguishedRootConeEvaluation_ker c.toMvPolynomial hirr hdegree r⁻¹ hrootInv
  have hhom : c.toMvPolynomial.IsHomogeneous 3 := by
    unfold Cubic.toMvPolynomial
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    convert (((MvPolynomial.isHomogeneous_C (Fin 4) (c i)).mul
      (MvPolynomial.isHomogeneous_X K i.1)).mul
        (MvPolynomial.isHomogeneous_X K i.2.1)).mul
          (MvPolynomial.isHomogeneous_X K i.2.2) using 1
  have hLI : LinearIndependent K (fun i => e (MvPolynomial.X i)) :=
    linearIndependent_coordinates_of_cubic_kernel c.toMvPolynomial hhom hirr.ne_zero e hbase hker
  rw [kollar_linePoint_eq_scaled_distinguishedRoot_coordinates r hr]
  exact cubic_generic_coordinates_linearIndependent_rescale _ hLI r hr

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness and a root of the actual generic residual already give the
no-contained-line conclusion for that center, over every further field E.
Only the smaller constant field K is assumed algebraically closed. -/
theorem kollar_residual_center_no_contained_line_of_smooth
    {K E : Type u} [Field K] [Field E] [IsAlgClosed K] [Algebra K E]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) E]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 3) K)) E]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    (r : E)
    (hroot : Polynomial.aeval r (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) = 0) :
    let x := (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))) +
      r • (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (kollarGenericProjectiveLineDirection K i))
    ∀ d : Fin 4 → E, LinearIndependent E ![x, d] →
      ∃ s t : E, (c.map (algebraMap K E)).eval (s • x + t • d) ≠ 0 := by
  let Q := FractionRing (MvPolynomial (Fin 3) K)
  let cQ := c.map (algebraMap K Q)
  let pQ := fun i => algebraMap K Q (kollarBasePoint K i)
  let dQ := kollarGenericProjectiveLineDirection K
  have hc0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hprime := principalIdeal_prime_of_smooth_homogeneous_cubic c.toMvPolynomial hhom hc0
  have hirr : Irreducible c.toMvPolynomial :=
    ((Ideal.span_singleton_prime hc0).mp hprime).irreducible
  have hdir : cQ.eval dQ ≠ 0 :=
    kollar_generic_projective_line_eval_ne_zero_of_smooth c.toMvPolynomial hhom c rfl hsec
  have hsecQ : cQ.mixed pQ dQ ≠ 0 :=
    kollar_generic_projective_line_secantCoefficient_ne_zero c hsec
  have hr : r ≠ 0 :=
    Cubic.lineResidual_root_ne_zero_of_mixed_ne_zero (algebraMap Q E)
      cQ pQ dQ hsecQ r hroot
  have hLI := kollar_residual_center_linearIndependent c hirr hp hsec hdir r hr hroot
  exact smoothCubic_generic_no_contained_line_through c.toMvPolynomial hhom hc0 c rfl _ hLI

set_option backward.isDefEq.respectTransparency false in
/-- The no-contained-line property of the generic residual center persists
through every field homomorphism, while the smaller algebraically closed
constant ground is retained through the induced scalar towers. -/
theorem kollar_residual_center_geometrically_no_contained_line_of_smooth
    {K E : Type u} [Field K] [Field E] [IsAlgClosed K] [Algebra K E]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) E]
    [IsScalarTower K (FractionRing (MvPolynomial (Fin 3) K)) E]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)]
    (r : E)
    (hroot : Polynomial.aeval r (Cubic.lineResidualPolynomial
      (c.map (algebraMap K (FractionRing (MvPolynomial (Fin 3) K))))
      (fun i => algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) = 0)
    (M : Type u) [Field M] (φ : E →+* M) :
    let x := (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))) +
      r • (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
        (kollarGenericProjectiveLineDirection K i))
    ∀ d : Fin 4 → M, LinearIndependent M ![(fun i => φ (x i)), d] →
      ∃ s t : M, ((c.map (algebraMap K E)).map φ).eval
        (s • (fun i => φ (x i)) + t • d) ≠ 0 := by
  let Q := FractionRing (MvPolynomial (Fin 3) K)
  letI : Algebra Q M := (φ.comp (algebraMap Q E)).toAlgebra
  letI : Algebra K M := (φ.comp (algebraMap K E)).toAlgebra
  letI : IsScalarTower K Q M := IsScalarTower.of_algebraMap_eq fun x => by
    change φ (algebraMap K E x) = φ (algebraMap Q E (algebraMap K Q x))
    rw [IsScalarTower.algebraMap_apply K Q E]
  have hrootM : Polynomial.aeval (φ r) (Cubic.lineResidualPolynomial
      (c.map (algebraMap K Q))
      (fun i => algebraMap K Q (kollarBasePoint K i))
      (kollarGenericProjectiveLineDirection K)) = 0 := by
    have h := congrArg φ hroot
    simp only [Polynomial.aeval_def] at h
    rw [map_zero, Polynomial.hom_eval₂] at h
    have hQE : algebraMap Q M = φ.comp (algebraMap Q E) := rfl
    change Polynomial.eval₂ (algebraMap Q M) (φ r) _ = 0
    rw [hQE]
    exact h
  have hc : (c.map (algebraMap K E)).map φ = c.map (algebraMap K M) := by
    funext i
    rfl
  have hx : (fun i => φ (((fun i => algebraMap Q E
        (algebraMap K Q (kollarBasePoint K i))) +
      r • (fun i => algebraMap Q E (kollarGenericProjectiveLineDirection K i))) i)) =
      (fun i => algebraMap Q M (algebraMap K Q (kollarBasePoint K i))) +
        (φ r) • (fun i => algebraMap Q M (kollarGenericProjectiveLineDirection K i)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    rfl
  dsimp only
  rw [hc, hx]
  exact kollar_residual_center_no_contained_line_of_smooth c hhom hp hsec (φ r) hrootM

end AllCharacteristics
