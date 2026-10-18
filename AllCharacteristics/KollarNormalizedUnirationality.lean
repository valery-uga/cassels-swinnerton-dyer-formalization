import AllCharacteristics.KollarNormalizedPolynomialConstruction
import AllCharacteristics.KollarNormalizedRawDetector
import AllCharacteristics.KollarDescendedPolynomialUnirationality
import AllCharacteristics.HomogeneousPrimeProjectiveIrreducibility

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized smooth cubic surface over an arbitrary field is
unirational, with the actual dominant rational map constructed from the two
conjugate residual tangent families. -/
theorem isUnirationalOver_normalized_smooth_cubic
    {k : Type u} [Field k] (c : Cubic k 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hp : c.eval (kollarBasePoint k) = 0)
    (hsec : c.mixed (kollarBasePoint k)
      (kollarAffineLineDirection k (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    IsUnirationalOver k (hypersurface c.toMvPolynomial hhom)
      (hypersurfaceToBase c.toMvPolynomial hhom) := by
  classical
  have hc0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hprime : (equationIdeal c.toMvPolynomial hhom).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic c.toMvPolynomial hhom hc0
  have hbp : kollarBasePoint k ≠ 0 := by
    intro hzero
    have hi := congrFun hzero 0
    simpa [kollarBasePoint] using hi
  have he : c.toMvPolynomial.eval₂ (RingHom.id k) (kollarBasePoint k) = 0 := by
    rw [Cubic.eval_toMvPolynomial]
    exact hp
  obtain ⟨P, _⟩ := hypersurface_point_of_coordinates (RingHom.id k)
    c.toMvPolynomial hhom (kollarBasePoint k) hbp he
  letI : IrreducibleSpace (hypersurface c.toMvPolynomial hhom) :=
    irreducibleSpace_of_prime_and_point (equationIdeal c.toMvPolynomial hhom)
      hprime (P (genericPoint (Spec (.of k))))
  letI : Fact (Irreducible (kollarGenericResidualPolynomial c)) :=
    ⟨kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec⟩
  letI : Fact (Irreducible (Cubic.lineResidualPolynomial
      (kollarGenericMappedCubic c) (kollarGenericMappedBasePoint k)
      (kollarGenericProjectiveLineDirection k))) := ⟨by
    change Irreducible (kollarGenericResidualPolynomial c)
    exact kollarGenericResidualPolynomial_irreducible_of_smooth c hhom hp hsec⟩
  obtain ⟨σ, j, s, R, hσ, hj, hs, hR, hRc⟩ :=
    exists_kollarNormalized_descended_polynomial_family c hhom hp hsec
  obtain ⟨hr, hdetect⟩ :=
    kollarNormalized_raw_secant_nonzero_and_detects c hhom hp hsec σ hσ j hj
  exact isUnirationalOver_of_kollar_descended_raw_detector c hhom
    (residualLineUniversalSecantPolynomial (kollarGenericMappedCubic c)
      (kollarGenericMappedBasePoint k) (kollarGenericProjectiveLineDirection k) σ j)
    R s hr hs hR hRc hdetect

end AllCharacteristics
