import AllCharacteristics.TangentRationalMap

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- A nonzero tangent--secant coordinate vector gives a rational map to the
cubic surface. This is the coordinate construction in the Segre--Manin
parametrization. -/
theorem rationalMap_of_tangentSecantResidual_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → k) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (u v : Fin 3 → X.functionField)
    (huv : Cubic.tangentSecantResidual (c.map φ.hom) (fun j ↦ φ.hom (p j))
      (tangentDirectionOfCoordinatesMap φ.hom c p hs u)
      (tangentDirectionOfCoordinatesMap φ.hom c p hs v) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_functionField_coordinates xbase F hF φ hφ
    (Cubic.tangentSecantResidual (c.map φ.hom) (fun j ↦ φ.hom (p j))
      (tangentDirectionOfCoordinatesMap φ.hom c p hs u)
      (tangentDirectionOfCoordinatesMap φ.hom c p hs v)) huv
  rw [← hc, Cubic.eval_toMvPolynomial]
  apply Cubic.eval_tangentSecantResidual
  · rw [Cubic.eval_map, hp, map_zero]
  · exact tangentDirectionOfCoordinatesMap_mem φ.hom c p hs u
  · exact tangentDirectionOfCoordinatesMap_mem φ.hom c p hs v

end HomogeneousProjective
end AllCharacteristics

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent

universe u

/-- Independence of the two residual tangent points and a nonzero secant
coefficient give the nonzero vector required by the tangent--secant map. -/
theorem rationalMap_of_tangentSecantResidual_coordinates_of_secant_conditions
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → k) (hp : c.eval p = 0)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (u v : Fin 3 → X.functionField)
    (hind : LinearIndependent X.functionField
      ![Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
          (tangentDirectionOfCoordinatesMap φ.hom c p hs u),
        Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
          (tangentDirectionOfCoordinatesMap φ.hom c p hs v)])
    (hsec : (c.map φ.hom).mixed
      (Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
        (tangentDirectionOfCoordinatesMap φ.hom c p hs u))
      (Cubic.tangentResidualPoint (c.map φ.hom) (fun j ↦ φ.hom (p j))
        (tangentDirectionOfCoordinatesMap φ.hom c p hs v)) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  apply rationalMap_of_tangentSecantResidual_coordinates
    xbase F hF c hc p hp hs φ hφ u v
  exact Cubic.tangentSecantResidual_ne_zero (c.map φ.hom) (fun j ↦ φ.hom (p j))
    (tangentDirectionOfCoordinatesMap φ.hom c p hs u)
    (tangentDirectionOfCoordinatesMap φ.hom c p hs v) hind hsec

end HomogeneousProjective
end AllCharacteristics
