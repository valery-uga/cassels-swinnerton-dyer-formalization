import PfaffianDescent.ActualPointTwistUntwistGammaScalar
import PfaffianDescent.ActualPositiveTwoGlobalLineEquiv

/- SOURCE ONLY / UNVERIFIED. Arbitrary ACTUAL positive-two point unit Isos
produce scalar-related untwist maps on genuine original Omega(2). -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualPositiveTwoTrivializedFiberEquiv
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (e : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf) :
    ActualCubicPositiveTwoPointDifferentialFiber p hp q ≃ₗ[L]
      ActualCubicPointDifferentialFiber p hp q :=
  ((moduleSpecΓFunctor (R := .of L)).mapIso
    (actualPositiveTwistPullbackTensorIso (equationIdeal p hp) q
      (schemeRelativeDifferentials (hypersurfaceToBase p hp)) 2 ≪≫
        actualPointTwistUntwistIso _ _ e)).toLinearEquiv

theorem actualPositiveTwoTrivializedFiberEquiv_scalar
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (e0 e1 : (Scheme.Modules.pullback q).obj
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2) ≅
        SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (w : ActualCubicPositiveTwoPointDifferentialFiber p hp q) :
    actualPositiveTwoTrivializedFiberEquiv p hp q e1 w =
      actualPointTwistTrivializationScalar e0 e1 •
        actualPositiveTwoTrivializedFiberEquiv p hp q e0 w := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of L)
  let M := (Scheme.Modules.pullback q).obj
    (schemeRelativeDifferentials (hypersurfaceToBase p hp))
  let T := (Scheme.Modules.pullback q).obj
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
  let C := actualPositiveTwistPullbackTensorIso (equationIdeal p hp) q
    (schemeRelativeDifferentials (hypersurfaceToBase p hp)) 2
  let U0 := actualPointTwistUntwistIso M T e0
  let U1 := actualPointTwistUntwistIso M T e1
  have h : F.map (C.hom ≫ U1.hom) w =
      F.map (U0.inv ≫ U1.hom) (F.map (C.hom ≫ U0.hom) w) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change F.map (C.hom ≫ U1.hom) w = _
  rw [h]
  exact actualPointTwistUntwist_ratio_gamma_scalar M T e0 e1 _

end PfaffianDescent
