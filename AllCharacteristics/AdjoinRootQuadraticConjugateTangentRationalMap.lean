import AllCharacteristics.QuadraticConjugateTangentRationalMap
import PfaffianDescent.CubicLineResidualGalois

open AlgebraicGeometry CategoryTheory Polynomial
open scoped AlgebraicGeometry

namespace AllCharacteristics
namespace HomogeneousProjective

open PfaffianDescent Module

universe u

/-- The conjugate-tangent secant construction gives a rational map directly
from a specified separable irreducible quadratic function-field extension. -/
theorem rationalMap_of_adjoinRoot_quadratic_conjugate_tangent_secant_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (xbase : X ⟶ Spec (.of k)) [IsIntegral X]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (c : Cubic k 4) (hc : c.toMvPolynomial = F)
    (φ : CommRingCat.of k ⟶ X.functionField)
    (hφ : Spec.map φ = X.fromSpecStalk _ ≫ xbase)
    (qpoly : X.functionField[X]) [Fact (Irreducible qpoly)]
    (hsep : qpoly.Separable) (hdegree : qpoly.natDegree = 2)
    (σ : AdjoinRoot qpoly ≃ₐ[X.functionField] AdjoinRoot qpoly)
    (hσne : σ ≠ AlgEquiv.refl)
    (p q dp dq : Vec (AdjoinRoot qpoly) 4)
    (hp : ((c.map φ.hom).map (algebraMap X.functionField (AdjoinRoot qpoly))).eval p = 0)
    (hq : ((c.map φ.hom).map (algebraMap X.functionField (AdjoinRoot qpoly))).eval q = 0)
    (htp : ((c.map φ.hom).map (algebraMap X.functionField (AdjoinRoot qpoly))).mixed p dp = 0)
    (htq : ((c.map φ.hom).map (algebraMap X.functionField (AdjoinRoot qpoly))).mixed q dq = 0)
    (hσp : (fun i => σ (p i)) = q) (hσq : (fun i => σ (q i)) = p)
    (hσdp : (fun i => σ (dp i)) = dq) (hσdq : (fun i => σ (dq i)) = dp)
    (hr0 : Cubic.secantResidualPoint ((c.map φ.hom).map
      (algebraMap X.functionField (AdjoinRoot qpoly)))
      (Cubic.tangentResidualPoint ((c.map φ.hom).map
        (algebraMap X.functionField (AdjoinRoot qpoly))) p dp)
      (Cubic.tangentResidualPoint ((c.map φ.hom).map
        (algebraMap X.functionField (AdjoinRoot qpoly))) q dq) ≠ 0) :
    ∃ f : X ⤏ hypersurface F hF,
      f.compHom (hypersurfaceToBase F hF) = xbase.toRationalMap := by
  have hirr : Irreducible qpoly := Fact.out
  let _ : FiniteDimensional X.functionField (AdjoinRoot qpoly) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let _ : Algebra.IsSeparable X.functionField (AdjoinRoot qpoly) :=
    adjoinRoot_isSeparable_of_irreducible_separable qpoly hirr hsep
  let _ : IsGalois X.functionField (AdjoinRoot qpoly) :=
    adjoinRoot_isGalois_of_irreducible_separable_natDegree_two hsep hdegree
  have hdim : finrank X.functionField (AdjoinRoot qpoly) = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact hdegree
  exact rationalMap_of_quadratic_conjugate_tangent_secant_coordinates
    xbase F hF c hc φ hφ (AdjoinRoot qpoly) σ hσne hdim
    p q dp dq hp hq htp htq hσp hσq hσdp hσdq hr0

end HomogeneousProjective
end AllCharacteristics
