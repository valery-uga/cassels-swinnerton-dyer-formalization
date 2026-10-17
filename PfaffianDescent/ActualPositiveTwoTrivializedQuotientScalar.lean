import PfaffianDescent.ActualPositiveTwoTrivializedFiberScalar

/- SOURCE ONLY / UNVERIFIED. The inverse scalar on quotient maps is derived
from actual tensor/unit action, not supplied as a coherence certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualPositiveTwoTrivializedQuotient
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (e : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp q →ₗ[L] L) :
    ActualCubicPointDifferentialFiber p hp q →ₗ[L] L :=
  ell.comp (actualPositiveTwoTrivializedFiberEquiv p hp q e).symm.toLinearMap

theorem actualPositiveTwoTrivializedQuotient_surjective
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (e : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp q →ₗ[L] L)
    (hell : Function.Surjective ell) :
    Function.Surjective (actualPositiveTwoTrivializedQuotient p hp q e ell) :=
  hell.comp (actualPositiveTwoTrivializedFiberEquiv p hp q e).symm.surjective

theorem actualPositiveTwoTrivializedQuotient_inverse_scalar
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (e0 e1 : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (ell : ActualCubicPositiveTwoPointDifferentialFiber p hp q →ₗ[L] L) :
    actualPositiveTwoTrivializedQuotient p hp q e1 ell =
      (actualPointTwistTrivializationScalar e0 e1)⁻¹ •
        actualPositiveTwoTrivializedQuotient p hp q e0 ell := by
  let E0 := actualPositiveTwoTrivializedFiberEquiv p hp q e0
  let E1 := actualPositiveTwoTrivializedFiberEquiv p hp q e1
  let c := actualPointTwistTrivializationScalar e0 e1
  have hc : c ≠ 0 := actualPointTwistTrivializationScalar_ne_zero e0 e1
  ext x
  have hInv : E1.symm x = c⁻¹ • E0.symm x := by
    apply E1.injective
    rw [E1.apply_symm_apply, E1.map_smul]
    change x = c⁻¹ • actualPositiveTwoTrivializedFiberEquiv p hp q e1 (E0.symm x)
    rw [actualPositiveTwoTrivializedFiberEquiv_scalar, E0.apply_symm_apply,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  change ell (E1.symm x) = c⁻¹ • ell (E0.symm x)
  rw [hInv, ell.map_smul]

end PfaffianDescent
