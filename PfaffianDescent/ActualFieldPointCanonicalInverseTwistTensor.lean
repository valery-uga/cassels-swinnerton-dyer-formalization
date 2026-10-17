import PfaffianDescent.ActualNegativeTwistPullbackTensorIso
import PfaffianDescent.ActualModuleLocalTensorInverseContraction
import PfaffianDescent.ActualFieldPointNegativeTwistTensorFiber
import PfaffianDescent.ActualPointLocalSectionClassNaturality

/-! SOURCE ONLY / UNVERIFIED. The actual canonical positive-negative
pairing, actual pullback tensor comparison and actual Γ tensor comparison
construct the untwisted source map. No desired Iso or comparison premise. -/
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
  (q : Spec (.of L) ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ)
local notation "P" => Scheme.Modules.pullback q
local notation "G" => moduleSpecΓFunctor (R := CommRingCat.of L)
local notation "Tplus" => positiveSheafOfModules (grading I) m
local notation "Tminus" => sheafOfModules (grading I) m
local notation "E" => ModuleCat.carrier (Functor.obj G
  (Functor.obj P (schemeModuleTensor M Tplus)))
local notation "B" => ModuleCat.carrier (ActualFieldPointNegativeTwistFiber I q m)

/-- The positive-then-negative insertion is the INVERSE COUNIT. The
functor of the installed twist equivalence tensors by the negative factor. -/
def actualFieldPointCanonicalInverseTwistTensorIso :
    (P).obj M ≅ schemeModuleTensor ((P).obj (schemeModuleTensor M Tplus))
      ((P).obj Tminus) :=
  (P).mapIso ((quotientTwistTensorRightEquivalence_all I m).counitIso.app M).symm ≪≫
    actualNegativeTwistPullbackTensorIso I q (schemeModuleTensor M Tplus) m

def actualFieldPointCanonicalInverseTwistTensorEquiv :
    ModuleCat.carrier ((G).obj ((P).obj M)) ≃ₗ[L] E ⊗[L] B :=
  ((G).mapIso (actualFieldPointCanonicalInverseTwistTensorIso I q M m)).toLinearEquiv ≪≫ₗ
    actualFieldPointNegativeTwistTensorFiberEquiv I q m
      ((P).obj (schemeModuleTensor M Tplus))

/- The installed counit is the actual contraction by the canonical
positive-negative pairing; equivalence construction preserves this counit. -/
set_option backward.isDefEq.respectTransparency false in
lemma actualTwistCounit_hom_eq_canonicalContraction :
    letI := quotientNegativeTwistComparison_isIso_all I m
      (PresheafOfModules.Monoidal.tensorObj M.val (Tplus).val)
    ((quotientTwistTensorRightEquivalence_all I m).counitIso.app M).hom =
      schemeModuleTensorContraction M Tplus Tminus
        (quotientPositiveNegativeTensorInverseIso_all I m) := by
  rfl

/- Actual canonical pairing comparison on genuine local pure sections.
The coefficient is the actual sheaf pairing, not a chosen coefficient-one
or a supplied frame compatibility equality. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldPointCanonicalInverseTwistTensorEquiv_localPairing
    (U : (scheme I).Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (w : M.val.obj (op U)) (n : (Tplus).val.obj (op U))
    (t : (Tminus).val.obj (op U)) :
    (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm
      ((actualPointLocalSectionClass q (schemeModuleTensor M Tplus) U hU
          (actualModuleLocalTensorSection M Tplus U w n)) ⊗ₜ[L]
        (actualPointLocalSectionClass q Tminus U hU t)) =
    actualPointLocalSectionClass q M U hU
      ((quotientPositiveNegativeTensorInverseIso_all I m).hom.val.app (op U)
        (actualModuleLocalTensorSection Tplus Tminus U n t) • w) := by
  let F := quotientTwistTensorRightEquivalence_all I m
  let A := schemeModuleTensor M Tplus
  let c := actualNegativeTwistPullbackTensorIso I q A m
  let theta := actualFieldPointNegativeTwistTensorFiberEquiv I q m ((P).obj A)
  let a := ((G).mapIso ((P).mapIso (F.counitIso.app M).symm)).toLinearEquiv
  let b := ((G).mapIso c).toLinearEquiv
  let z := actualPointLocalSectionClass q (schemeModuleTensor A Tminus) U hU
    (actualModuleLocalTensorSection A Tminus U
      (actualModuleLocalTensorSection M Tplus U w n) t)
  have hsplit : theta (b z) =
      (actualPointLocalSectionClass q A U hU
        (actualModuleLocalTensorSection M Tplus U w n)) ⊗ₜ[L]
      (actualPointLocalSectionClass q Tminus U hU t) := by
    have hc := actualPointLocalTensorPullbackAction q A Tminus U hU
      (actualModuleLocalTensorSection M Tplus U w n) t
    have ht := actualFieldPointNegativeTwistTensorFiberEquiv_pureSection I q m
      ((P).obj A)
      (actualPointLocalSectionClass q A U hU
        (actualModuleLocalTensorSection M Tplus U w n))
      (actualPointLocalSectionClass q Tminus U hU t)
    exact (congrArg theta hc).trans ht
  have hinv : (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm
      (theta (b z)) = a.symm z := by
    change (((a ≪≫ₗ b) ≪≫ₗ theta).symm (theta (b z))) = a.symm z
    simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]
    exact congrArg a.symm (b.symm_apply_apply z)
  have hnat := actualPointLocalSectionClass_naturality q
    (F.counitIso.app M).hom U hU
    (actualModuleLocalTensorSection A Tminus U
      (actualModuleLocalTensorSection M Tplus U w n) t)
  letI := quotientNegativeTwistComparison_isIso_all I m
    (PresheafOfModules.Monoidal.tensorObj M.val (Tplus).val)
  have hpair := actualModuleLocalTensorInverseContraction M Tplus Tminus
    (quotientPositiveNegativeTensorInverseIso_all I m) U w n t
  have hcontraction : (F.counitIso.app M).hom.val.app (op U)
      (actualModuleLocalTensorSection A Tminus U
        (actualModuleLocalTensorSection M Tplus U w n) t) =
      (quotientPositiveNegativeTensorInverseIso_all I m).hom.val.app (op U)
        (actualModuleLocalTensorSection Tplus Tminus U n t) • w := by
    have he := actualTwistCounit_hom_eq_canonicalContraction I M m
    have heval := congrArg
      (fun f : schemeModuleTensor (schemeModuleTensor M Tplus) Tminus ⟶ M =>
        (SheafOfModules.Hom.val f).app (op U)
          (actualModuleLocalTensorSection A Tminus U
            (actualModuleLocalTensorSection M Tplus U w n) t)) he
    dsimp only [F]
    exact heval.trans hpair
  calc
    (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm
        ((actualPointLocalSectionClass q A U hU
            (actualModuleLocalTensorSection M Tplus U w n)) ⊗ₜ[L]
          (actualPointLocalSectionClass q Tminus U hU t)) = a.symm z :=
      (congrArg (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm
        hsplit.symm).trans hinv
    _ = (G).map ((P).map (F.counitIso.app M).hom) z := rfl
    _ = actualPointLocalSectionClass q M U hU
        ((F.counitIso.app M).hom.val.app (op U)
          (actualModuleLocalTensorSection A Tminus U
            (actualModuleLocalTensorSection M Tplus U w n) t)) := hnat
    _ = actualPointLocalSectionClass q M U hU
        ((quotientPositiveNegativeTensorInverseIso_all I m).hom.val.app (op U)
          (actualModuleLocalTensorSection Tplus Tminus U n t) • w) :=
      congrArg (actualPointLocalSectionClass q M U hU) hcontraction

end
end PfaffianDescent
