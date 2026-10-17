import PfaffianDescent.ActualFieldPointNegativeTwistUnitIso
import PfaffianDescent.ActualPointLocalTensorUnitContraction
import PfaffianDescent.ActualPointLocalTwistResidueCoefficient
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! SOURCE ONLY / UNVERIFIED. A small actual Γ tensor comparison when the
right factor is the native negative twist at the SAME field point. Its
trivialization is derived internally, never supplied. The pure-section law
identifies this comparison with the actual sheafification tensor unit. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L : Type u} [Field K] [Field L]
  (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
  (q : Spec (.of L) ⟶ scheme I) (m : ℕ)
local notation "T" => Functor.obj (Scheme.Modules.pullback q) (sheafOfModules (grading I) m)
local notation "G" => moduleSpecΓFunctor (R := CommRingCat.of L)
local notation "B" => ActualFieldPointNegativeTwistFiber I q m

def actualFieldPointNegativeTwistTensorFiberEquiv
    (M : (Spec (.of L)).Modules) :
    (G).obj (schemeModuleTensor M T) ≃ₗ[L] ((G).obj M) ⊗[L] B :=
  ((G).mapIso (actualPointTwistUntwistIso M T
    (actualFieldPointNegativeTwistUnitIso I q m))).toLinearEquiv ≪≫ₗ
      ((TensorProduct.congr (LinearEquiv.refl L ((G).obj M))
        (actualFieldPointNegativeTwistFiberEquiv I q m)) ≪≫ₗ
          TensorProduct.rid L ((G).obj M)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldPointNegativeTwistTensorFiberEquiv_pureSection
    (M : (Spec (.of L)).Modules) (x : (G).obj M) (t : B) :
    actualFieldPointNegativeTwistTensorFiberEquiv I q m M
      (actualModuleLocalTensorSection M T ⊤ x t) = x ⊗ₜ[L] t := by
  let e := actualFieldPointNegativeTwistUnitIso I q m
  let b := actualFieldPointNegativeTwistFiberEquiv I q m
  let a := ((G).mapIso (actualPointTwistUntwistIso M T e)).toLinearEquiv
  let v := (TensorProduct.congr (LinearEquiv.refl L ((G).obj M)) b) ≪≫ₗ
    TensorProduct.rid L ((G).obj M)
  apply v.injective
  have h := actualPointTwistUntwistIso_localTensorSection M T e x t
  let c : Γ(Spec (.of L), ⊤) := e.hom.val.app (op ⊤) t
  have hcoeff : b t • x = c • (show Γ(M, ⊤) from x) := by
    change (Scheme.ΓSpecIso (.of L)).hom.hom c • x =
      c • (show Γ(M, ⊤) from x)
    exact (actualFieldGammaScalar_eq_residueScalar M c x).symm
  calc
    v (actualFieldPointNegativeTwistTensorFiberEquiv I q m M
        (actualModuleLocalTensorSection M T ⊤ x t)) =
        a (actualModuleLocalTensorSection M T ⊤ x t) :=
      v.apply_symm_apply _
    _ = c • (show Γ(M, ⊤) from x) := h
    _ = b t • x := hcoeff.symm
    _ = v (x ⊗ₜ[L] t) := by
      simp only [v, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, TensorProduct.rid_tmul]

end
end PfaffianDescent
