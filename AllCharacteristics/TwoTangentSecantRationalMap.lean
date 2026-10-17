import AllCharacteristics.SecantRationalMap
import PfaffianDescent.CubicSecant
import PfaffianDescent.MultivariateCubic

/-!
# Third-intersection maps from two tangent residual curves

This packages the last coordinate operation in the Segre--Manin--Kollár
construction: take a residual point on each of two tangent sections, then
take the third point of their secant line.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- Two tangent residual points whose secant is genuine give a rational map to
the cubic hypersurface. -/
theorem rationalMap_of_two_tangentResidual_secant_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (p q dp dq : Fin 4 → X.functionField)
    (hp : (c.map φ.hom).eval p = 0) (hq : (c.map φ.hom).eval q = 0)
    (htp : (c.map φ.hom).mixed p dp = 0)
    (htq : (c.map φ.hom).mixed q dq = 0)
    (hind : LinearIndependent X.functionField
      ![Cubic.tangentResidualPoint (c.map φ.hom) p dp,
        Cubic.tangentResidualPoint (c.map φ.hom) q dq])
    (hsec : (c.map φ.hom).mixed
      (Cubic.tangentResidualPoint (c.map φ.hom) p dp)
      (Cubic.tangentResidualPoint (c.map φ.hom) q dq) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_secantResidual_coordinates_of_secant_conditions
    xbase F hF c hc φ hφ
    (Cubic.tangentResidualPoint (c.map φ.hom) p dp)
    (Cubic.tangentResidualPoint (c.map φ.hom) q dq)
  · exact Cubic.eval_tangentResidualPoint (c.map φ.hom) p dp hp htp
  · exact Cubic.eval_tangentResidualPoint (c.map φ.hom) q dq hq htq
  · exact hind
  · exact hsec

end HomogeneousProjective
end AllCharacteristics
