import AllCharacteristics.SmoothCubicGenericSecantPreimage
import AllCharacteristics.KollarResidualCenterGenericity

/-! Geometric center no-line properties compose through
the explicit root-field embedding and its algebraic closure. -/

noncomputable section
namespace AllCharacteristics
open PfaffianDescent AlgebraicGeometry HomogeneousProjective
universe u

theorem GeometricallyNoContainedLineThrough.map
    {L K : Type u} [Field L] [Field K]
    (c : Cubic L 4) (p : Fin 4 → L)
    (h : GeometricallyNoContainedLineThrough c p) (β : L →+* K) :
    GeometricallyNoContainedLineThrough (c.map β) (fun i => β (p i)) := by
  intro M _ g
  exact h M (g.comp β)

/-- The reciprocal-kernel argument gives the exact geometric center property
required by the frame-free two-tangent secant endpoint. -/
theorem kollar_residual_center_geometricallyNoContainedLine
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
    GeometricallyNoContainedLineThrough (c.map (algebraMap K E))
      ((fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
          (algebraMap K (FractionRing (MvPolynomial (Fin 3) K)) (kollarBasePoint K i))) +
        r • (fun i => algebraMap (FractionRing (MvPolynomial (Fin 3) K)) E
          (kollarGenericProjectiveLineDirection K i))) := by
  intro M _ φ
  exact kollar_residual_center_geometrically_no_contained_line_of_smooth
    c hhom hp hsec r hroot M φ

end AllCharacteristics
