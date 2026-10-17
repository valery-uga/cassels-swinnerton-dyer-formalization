import AllCharacteristics.RationalMapCoordinates
import PfaffianDescent.QuadraticConjugateDescent
import PfaffianDescent.MultivariateCubic

/-!
# Rational maps from quadratic-conjugate tangent residuals

This is the function-field descent step in the two-conjugate-tangent
construction.  It converts the anti-invariant third-intersection coordinates
over a quadratic Galois extension into a rational map over the original
ground field.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent Module

universe u

/-- The third-intersection coordinates of two conjugate tangent residuals over
an actual quadratic Galois extension descend to the source function field and
therefore define a rational map to the original cubic hypersurface. -/
theorem rationalMap_of_quadratic_conjugate_tangent_secant_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L]
    (σ : L ≃ₐ[X.functionField] L) (hσne : σ ≠ AlgEquiv.refl)
    (hdim : finrank X.functionField L = 2)
    (p q dp dq : Vec L 4)
    (hp : ((c.map φ.hom).map (algebraMap X.functionField L)).eval p = 0)
    (hq : ((c.map φ.hom).map (algebraMap X.functionField L)).eval q = 0)
    (htp : ((c.map φ.hom).map (algebraMap X.functionField L)).mixed p dp = 0)
    (htq : ((c.map φ.hom).map (algebraMap X.functionField L)).mixed q dq = 0)
    (hσp : (fun i => σ (p i)) = q) (hσq : (fun i => σ (q i)) = p)
    (hσdp : (fun i => σ (dp i)) = dq) (hσdq : (fun i => σ (dq i)) = dp)
    (hr0 : Cubic.secantResidualPoint ((c.map φ.hom).map (algebraMap X.functionField L))
      (Cubic.tangentResidualPoint ((c.map φ.hom).map (algebraMap X.functionField L)) p dp)
      (Cubic.tangentResidualPoint ((c.map φ.hom).map (algebraMap X.functionField L)) q dq) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  obtain ⟨a, ha, hca⟩ :=
    exists_base_cubic_point_of_conjugate_tangent_secant σ hσne hdim
      (c.map φ.hom) p q dp dq hp hq htp htq hσp hσq hσdp hσdq hr0
  apply rationalMap_of_functionField_coordinates xbase F hF φ hφ a ha
  rw [← hc, Cubic.eval_toMvPolynomial]
  exact hca

end HomogeneousProjective
end AllCharacteristics
