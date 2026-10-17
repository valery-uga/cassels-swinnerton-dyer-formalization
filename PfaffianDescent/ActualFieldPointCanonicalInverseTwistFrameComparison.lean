import PfaffianDescent.ActualFieldPointCanonicalTwistPairingScalar
import PfaffianDescent.ActualFieldPointCanonicalInverseTwistTensor

/-! SOURCE ONLY / UNVERIFIED. The canonical inverse-pairing source map
and the independently derived positive/negative frames differ by the
DERIVED nonzero actual pairing coefficient on ALL native fiber elements. -/
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
local notation "W" => ModuleCat.carrier
  (Functor.obj (moduleSpecΓFunctor (R := CommRingCat.of L))
    (Functor.obj (Scheme.Modules.pullback q) M))
local notation "E" => ModuleCat.carrier
  (Functor.obj (moduleSpecΓFunctor (R := CommRingCat.of L))
    (Functor.obj (Scheme.Modules.pullback q) (schemeModuleTensor M Tplus)))
local notation "B" => ModuleCat.carrier
  (ActualFieldPointNegativeTwistFiber (K := K) (L := L) I q m)
local notation "Uplus" => Iso.toLinearEquiv
  (Functor.mapIso (moduleSpecΓFunctor (R := CommRingCat.of L))
    (actualFieldPointPositiveTwistTensorUntwistIso (K := K) (L := L) I q M m))
local notation "bminus" => actualFieldPointNegativeTwistFiberEquiv (K := K) (L := L) I q m
local notation "alpha" => actualFieldPointCanonicalTwistPairingScalar (K := K) (L := L) I q m
local notation "Rtop" => CommRingCat.carrier
  (Functor.obj
    (PresheafedSpace.presheaf
      (SheafedSpace.toPresheafedSpace
        (LocallyRingedSpace.toSheafedSpace
          (Scheme.toLocallyRingedSpace (Spec (CommRingCat.of L))))))
    (op (α := Scheme.Opens (Spec (CommRingCat.of L))) ⊤))
local notation "n₁" => PresheafOfModules.Hom.app
  (SheafOfModules.Hom.val (Iso.inv (actualFieldPointPositiveTwistUnitIso I q m)))
  (op ⊤) (1 : Rtop)
local notation "t₁" => PresheafOfModules.Hom.app
  (SheafOfModules.Hom.val (Iso.inv (actualFieldPointNegativeTwistUnitIso I q m)))
  (op ⊤) (1 : Rtop)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma positiveComparison_untwist_inverse (w : W) :
    (G).map (actualPositiveTwistPullbackTensorIso I q M m).hom ((Uplus).symm w) =
      actualModuleLocalTensorSection ((P).obj M) ((P).obj Tplus) ⊤ w n₁ := by
  let c := actualPositiveTwistPullbackTensorIso I q M m
  let e := actualFieldPointPositiveTwistUnitIso I q m
  let a := ((G).mapIso (actualPointTwistUntwistIso ((P).obj M) ((P).obj Tplus) e)).toLinearEquiv
  apply a.injective
  have h₁ := congrArg (fun v => v.val.app (op ⊤) (1 : Rtop)) e.inv_hom_id
  change e.hom.val.app (op ⊤) n₁ = (1 : Rtop) at h₁
  have hp := actualPointTwistUntwistIso_localTensorSection ((P).obj M) ((P).obj Tplus)
    e w n₁
  rw [h₁, one_smul] at hp
  have hc : a ((G).map c.hom ((Uplus).symm w)) = w := by
    change (G).map (actualPointTwistUntwistIso ((P).obj M) ((P).obj Tplus) e).hom
      ((G).map c.hom ((Uplus).symm w)) = w
    rw [← ModuleCat.comp_apply, ← Functor.map_comp]
    change Uplus ((Uplus).symm w) = w
    exact (Uplus).apply_symm_apply w
  exact hc.trans hp.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma canonicalInverse_on_tmul (x : E) (t : B) :
    letI := schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
      (PresheafOfModules.Monoidal.tensorObj ((P).obj M).val ((P).obj Tplus).val)
      (actualFieldPointNegativeTwistUnitIso I q m)
    (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm (x ⊗ₜ[L] t) =
      (G).map (schemeModuleTensorContraction ((P).obj M) ((P).obj Tplus) ((P).obj Tminus)
        (actualFieldPointCanonicalTwistPairingIso I q m))
        (actualModuleLocalTensorSection (schemeModuleTensor ((P).obj M) ((P).obj Tplus))
          ((P).obj Tminus) ⊤
          ((G).map (actualPositiveTwistPullbackTensorIso I q M m).hom x) t) := by
  letI := quotientNegativeTwistComparison_isIso_all I m
    (PresheafOfModules.Monoidal.tensorObj M.val (Tplus).val)
  letI := schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
    (PresheafOfModules.Monoidal.tensorObj ((P).obj M).val ((P).obj Tplus).val)
    (actualFieldPointNegativeTwistUnitIso I q m)
  let A := schemeModuleTensor M Tplus
  let F := quotientTwistTensorRightEquivalence_all I m
  let cNeg := actualNegativeTwistPullbackTensorIso I q A m
  let cPos := actualPositiveTwistPullbackTensorIso I q M m
  let Dp := schemeModuleTensorContraction ((P).obj M) ((P).obj Tplus) ((P).obj Tminus)
    (actualFieldPointCanonicalTwistPairingIso I q m)
  let theta := actualFieldPointNegativeTwistTensorFiberEquiv I q m ((P).obj A)
  have hcoh : (P).map (F.counitIso.app M).hom =
      cNeg.hom ≫ schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp := by
    rw [actualTwistCounit_hom_eq_canonicalContraction]
    exact actualFieldPointCanonicalTwistContraction_pullback I q m M
  have hi : cNeg.inv ≫ (P).map (F.counitIso.app M).hom =
      schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp := by
    rw [hcoh, Iso.inv_hom_id_assoc]
  have htheta : theta.symm (x ⊗ₜ[L] t) =
      actualModuleLocalTensorSection ((P).obj A) ((P).obj Tminus) ⊤ x t := by
    exact (congrArg theta.symm
      (actualFieldPointNegativeTwistTensorFiberEquiv_pureSection I q m ((P).obj A) x t)).symm.trans
        (theta.symm_apply_apply _)
  have ht := actualModuleLocalTensorSection_naturality cPos.hom (𝟙 ((P).obj Tminus)) ⊤ x t
  calc
    (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm (x ⊗ₜ[L] t) =
      (G).map (cNeg.inv ≫ (P).map (F.counitIso.app M).hom) (theta.symm (x ⊗ₜ[L] t)) := by
        rfl
    _ = (G).map (schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp)
        (actualModuleLocalTensorSection ((P).obj A) ((P).obj Tminus) ⊤ x t) :=
      (congrArg (fun f => (G).map f (theta.symm (x ⊗ₜ[L] t))) hi).trans
        (congrArg ((G).map (schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp))
          htheta)
    _ = (G).map Dp
        (actualModuleLocalTensorSection (schemeModuleTensor ((P).obj M) ((P).obj Tplus))
          ((P).obj Tminus) ⊤ ((G).map cPos.hom x) t) := by
      simp only [Functor.map_comp, ModuleCat.comp_apply]
      have hid : (SheafOfModules.Hom.val (𝟙 ((P).obj Tminus))).app (op ⊤) t = t := rfl
      have ht' : (G).map (schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)))
          (actualModuleLocalTensorSection ((P).obj A) ((P).obj Tminus) ⊤ x t) =
          actualModuleLocalTensorSection
            (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤
            ((G).map cPos.hom x) t :=
        ht.trans (congrArg
          (fun y : Γ((P).obj Tminus, ⊤) =>
            actualModuleLocalTensorSection
              (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤
              ((G).map cPos.hom x) y) hid)
      exact congrArg ((G).map Dp) ht'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualFieldPointCanonicalInverseTwistTensorEquiv_frame (w : W) :
    (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m).symm
      ((Uplus).symm w ⊗ₜ[L] (bminus).symm 1) = alpha • w := by
  letI := schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
    (PresheafOfModules.Monoidal.tensorObj ((P).obj M).val ((P).obj Tplus).val)
    (actualFieldPointNegativeTwistUnitIso I q m)
  let ep := actualFieldPointCanonicalTwistPairingIso I q m
  let r : Γ(Spec (.of L), ⊤) := ep.hom.val.app (op ⊤)
    (actualModuleLocalTensorSection ((P).obj Tplus) ((P).obj Tminus) ⊤ n₁ t₁)
  let J : W ≃ₗ[L] E ⊗[L] B := actualFieldPointCanonicalInverseTwistTensorEquiv I q M m
  let Dp : schemeModuleTensor (schemeModuleTensor ((P).obj M) ((P).obj Tplus))
      ((P).obj Tminus) ⟶ (P).obj M :=
    schemeModuleTensorContraction ((P).obj M) ((P).obj Tplus) ((P).obj Tminus) ep
  let z : Γ(schemeModuleTensor (schemeModuleTensor ((P).obj M) ((P).obj Tplus))
      ((P).obj Tminus), ⊤) :=
    actualModuleLocalTensorSection (schemeModuleTensor ((P).obj M) ((P).obj Tplus))
      ((P).obj Tminus) ⊤
      (actualModuleLocalTensorSection ((P).obj M) ((P).obj Tplus) ⊤ w n₁) t₁
  have h : J.symm ((Uplus).symm w ⊗ₜ[L] (bminus).symm 1) = (G).map Dp z := by
    have hraw : J.symm ((Uplus).symm w ⊗ₜ[L] (bminus).symm 1) =
        (G).map Dp
          (actualModuleLocalTensorSection
            (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤
            ((G).map (actualPositiveTwistPullbackTensorIso I q M m).hom ((Uplus).symm w))
            ((bminus).symm 1)) :=
      canonicalInverse_on_tmul I q M m ((Uplus).symm w) ((bminus).symm 1)
    have hpos : (G).map (actualPositiveTwistPullbackTensorIso I q M m).hom ((Uplus).symm w) =
        actualModuleLocalTensorSection ((P).obj M) ((P).obj Tplus) ⊤ w n₁ :=
      positiveComparison_untwist_inverse I q M m w
    have hneg : (bminus).symm 1 = t₁ :=
      (actualFieldPointNegativeFrame_eq_fiberEquiv_symm_one (K := K) (L := L) I q m).symm
    have hsection : actualModuleLocalTensorSection
        (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤
        ((G).map (actualPositiveTwistPullbackTensorIso I q M m).hom ((Uplus).symm w))
        ((bminus).symm 1) = z :=
      congrArg₂
        (fun (x : Γ(schemeModuleTensor ((P).obj M) ((P).obj Tplus), ⊤))
          (t : Γ((P).obj Tminus, ⊤)) =>
          actualModuleLocalTensorSection
            (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤ x t)
        hpos hneg
    exact hraw.trans (congrArg ((G).map Dp) hsection)
  have hd : (G).map Dp z = r • (show Γ((P).obj M, ⊤) from w) :=
    actualModuleLocalTensorInverseContraction ((P).obj M) ((P).obj Tplus)
      ((P).obj Tminus) ep ⊤ w n₁ t₁
  have hc : r • (show Γ((P).obj M, ⊤) from w) = alpha • w := by
    have ha := actualFieldPointCanonicalTwistPairingScalar_eval I q m
    change (Scheme.ΓSpecIso (.of L)).hom.hom r = alpha at ha
    rw [← ha]
    exact actualFieldGammaScalar_eq_residueScalar ((P).obj M) r w
  calc
    J.symm ((Uplus).symm w ⊗ₜ[L] (bminus).symm 1) = (G).map Dp z := h
    _ = r • (show Γ((P).obj M, ⊤) from w) := hd
    _ = alpha • w := hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full canonical map is the derived-frame map multiplied by the
inverse actual pairing coefficient. No desired scalar equality is assumed. -/
theorem actualFieldPointCanonicalInverseTwistTensorEquiv_apply (w : W) :
    actualFieldPointCanonicalInverseTwistTensorEquiv I q M m w =
      alpha⁻¹ • ((Uplus).symm w ⊗ₜ[L] (bminus).symm 1) := by
  let J := actualFieldPointCanonicalInverseTwistTensorEquiv I q M m
  apply J.symm.injective
  rw [J.symm_apply_apply, LinearEquiv.map_smul,
    actualFieldPointCanonicalInverseTwistTensorEquiv_frame]
  rw [smul_smul, inv_mul_cancel₀ (actualFieldPointCanonicalTwistPairingScalar_ne_zero I q m),
    one_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal tensor(q,id) contracted to the original target has the inverse
actual pairing coefficient, for every actual target and every fiber element. -/
theorem actualFieldPointCanonicalTensorQuotient_contract
    {N : Type u} [AddCommGroup N] [Module L N] (qLin : E →ₗ[L] N) (w : W) :
    let target := (TensorProduct.congr (LinearEquiv.refl L N) bminus) ≪≫ₗ
      TensorProduct.rid L N
    target (TensorProduct.map qLin (LinearMap.id : B →ₗ[L] B)
      (actualFieldPointCanonicalInverseTwistTensorEquiv I q M m w)) =
        alpha⁻¹ • qLin ((Uplus).symm w) := by
  rw [actualFieldPointCanonicalInverseTwistTensorEquiv_apply]
  simp only [LinearMap.map_smul, LinearEquiv.map_smul, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply, TensorProduct.rid_tmul,
    one_smul]

end
end PfaffianDescent
