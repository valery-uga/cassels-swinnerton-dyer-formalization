import AllCharacteristics.RationalMapCoordinates
import PfaffianDescent.CubicSecant
import PfaffianDescent.MultivariateCubic

/-!
# Rational maps from secant-residual coordinates

A pair of generic points on a cubic hypersurface determines its third
intersection point.  This file turns nonzero secant-residual coordinates in a
function field into a rational map to the cubic surface.  It is the
scheme-theoretic target step in the two-tangent-curve construction used for
unirationality.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- Nonzero generic secant-residual coordinates give a rational map to the
cubic hypersurface. -/
theorem rationalMap_of_secantResidual_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (p q : Fin 4 → X.functionField)
    (hp : (c.map φ.hom).eval p = 0) (hq : (c.map φ.hom).eval q = 0)
    (hpq : Cubic.secantResidualPoint (c.map φ.hom) p q ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_functionField_coordinates xbase F hF φ hφ
    (Cubic.secantResidualPoint (c.map φ.hom) p q) hpq
  rw [← hc, Cubic.eval_toMvPolynomial]
  exact Cubic.eval_secantResidualPoint (c.map φ.hom) p q hp hq

/-- Linear independence of the two generic cubic points and a nonzero secant
coefficient imply the coordinate nonvanishing required for the secant map. -/
theorem rationalMap_of_secantResidual_coordinates_of_secant_conditions
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (p q : Fin 4 → X.functionField)
    (hp : (c.map φ.hom).eval p = 0) (hq : (c.map φ.hom).eval q = 0)
    (hind : LinearIndependent X.functionField ![p, q])
    (hsec : (c.map φ.hom).mixed p q ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_secantResidual_coordinates xbase F hF c hc φ hφ p q hp hq
  exact Cubic.secantResidualPoint_ne_zero (c.map φ.hom) p q hind hsec

end HomogeneousProjective
end AllCharacteristics
