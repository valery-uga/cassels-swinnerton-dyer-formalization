import AllCharacteristics.RationalMapCoordinates
import AllCharacteristics.SmoothCubicTangent

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- A nonzero residual tangent coordinate vector gives a rational map to the
cubic surface over the base field. -/
theorem rationalMap_of_tangentResidual_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → k) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (u : Fin 3 → X.functionField)
    (hu : Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
      (tangentDirectionOfCoordinatesMap φ.hom c p hs u) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_functionField_coordinates xbase F hF φ hφ
    (Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
      (tangentDirectionOfCoordinatesMap φ.hom c p hs u)) hu
  rw [← hc, Cubic.eval_toMvPolynomial]
  exact eval_tangentResidualPoint_tangentDirectionOfCoordinatesMap φ.hom c p hp hs u

end HomogeneousProjective
end AllCharacteristics

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- A direction whose cubic value is nonzero supplies the nonzero residual
coordinate vector needed for the tangent rational map. -/
theorem rationalMap_of_tangentResidual_coordinates_of_eval_ne_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → k) (hp0 : p ≠ 0) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (u : Fin 3 → X.functionField)
    (hu : (c.map φ.hom).eval
      (tangentDirectionOfCoordinatesMap φ.hom c p hs u) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_tangentResidual_coordinates xbase F hF c hc p hp hs φ hφ u
  apply Cubic.tangentResidualPoint_ne_zero_of_eval_ne_zero
  · intro h
    apply hp0
    funext i
    apply φ.hom.injective
    simpa using congrFun h i
  · rw [Cubic.eval_map, hp, map_zero]
  · exact hu

end HomogeneousProjective
end AllCharacteristics
