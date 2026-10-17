import PfaffianDescent.ActualFieldPointCanonicalTwistContraction
import PfaffianDescent.ActualFieldUnitAutomorphismScalar

/-! SOURCE ONLY / UNVERIFIED. The actual positive and negative field-point
frames compute the canonical pairing's coefficient. Its nonvanishing is
derived from the actual unit automorphism, not assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L : Type u} [Field K] [Field L]
  (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
  (q : Spec (.of L) ⟶ scheme I) (m : ℕ)
local notation "P" => Scheme.Modules.pullback q
local notation "G" => moduleSpecΓFunctor (R := CommRingCat.of L)
local notation "O" => SheafOfModules.unit (Scheme.ringCatSheaf (Spec (CommRingCat.of L)))
local notation "Tplus" => positiveSheafOfModules (grading I) m
local notation "Tminus" => sheafOfModules (grading I) m
local notation "e₊" => actualFieldPointPositiveTwistUnitIso I q m
local notation "e₋" => actualFieldPointNegativeTwistUnitIso I q m
local notation "Rtop" => CommRingCat.carrier
  (Functor.obj
    (PresheafedSpace.presheaf
      (SheafedSpace.toPresheafedSpace
        (LocallyRingedSpace.toSheafedSpace
          (Scheme.toLocallyRingedSpace (Spec (CommRingCat.of L))))))
    (op (α := Scheme.Opens (Spec (CommRingCat.of L))) ⊤))
local notation "n₁" => PresheafOfModules.Hom.app
  (SheafOfModules.Hom.val (Iso.inv e₊)) (op ⊤) (1 : Rtop)
local notation "t₁" => PresheafOfModules.Hom.app
  (SheafOfModules.Hom.val (Iso.inv e₋)) (op ⊤) (1 : Rtop)

def actualFieldPointTwistFramesPairUnitIso :
    schemeModuleTensor ((P).obj Tplus) ((P).obj Tminus) ≅ O :=
  schemeModuleTensorMapIso e₊ e₋ ≪≫ schemeModuleTensorUnitRightIso O

def actualFieldPointCanonicalTwistPairingScalar : L :=
  actualFieldUnitAutomorphismScalar
    ((actualFieldPointTwistFramesPairUnitIso I q m).inv ≫
      (actualFieldPointCanonicalTwistPairingIso I q m).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualFieldPointCanonicalTwistPairingScalar_ne_zero :
    actualFieldPointCanonicalTwistPairingScalar I q m ≠ 0 := by
  let f := actualFieldPointTwistFramesPairUnitIso I q m
  let e := actualFieldPointCanonicalTwistPairingIso I q m
  let a : O ≅ O := f.symm ≪≫ e
  letI : IsIso (f.inv ≫ e.hom) := a.isIso_hom
  exact @actualFieldUnitAutomorphismScalar_ne_zero L _ (f.inv ≫ e.hom)
    (show IsIso (f.inv ≫ e.hom) from a.isIso_hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pairedFrames_inverse_one :
    (actualFieldPointTwistFramesPairUnitIso I q m).inv.val.app (op ⊤)
      (1 : Rtop) =
      actualModuleLocalTensorSection ((P).obj Tplus) ((P).obj Tminus) ⊤ n₁ t₁ := by
  let f := actualFieldPointTwistFramesPairUnitIso I q m
  apply ((G).mapIso f).toLinearEquiv.injective
  have hi := congrArg (fun v => (SheafOfModules.Hom.val v).app (op ⊤) (1 : Rtop)) f.inv_hom_id
  have hPlus := congrArg (fun v => (SheafOfModules.Hom.val v).app (op ⊤) (1 : Rtop)) (e₊).inv_hom_id
  have hMinus := congrArg (fun v => (SheafOfModules.Hom.val v).app (op ⊤) (1 : Rtop)) (e₋).inv_hom_id
  have ht := actualModuleLocalTensorSection_naturality (e₊).hom (e₋).hom ⊤ n₁ t₁
  have hr := actualModuleLocalTensorRightUnitAction O ⊤
    (1 : Rtop) (1 : Rtop)
  change f.hom.val.app (op ⊤) (f.inv.val.app (op ⊤) (1 : Rtop)) =
    (schemeModuleTensorUnitRightIso O).hom.val.app (op ⊤)
      ((schemeModuleTensorMap (e₊).hom (e₋).hom).val.app (op ⊤)
        (actualModuleLocalTensorSection ((P).obj Tplus) ((P).obj Tminus) ⊤ n₁ t₁))
  rw [ht]
  change _ = (schemeModuleTensorUnitRightIso O).hom.val.app (op ⊤)
    (actualModuleLocalTensorSection O O ⊤
      ((e₊).hom.val.app (op ⊤) n₁) ((e₋).hom.val.app (op ⊤) t₁))
  change (e₊).hom.val.app (op ⊤) n₁ = (1 : Rtop) at hPlus
  change (e₋).hom.val.app (op ⊤) t₁ = (1 : Rtop) at hMinus
  change f.hom.val.app (op ⊤) (f.inv.val.app (op ⊤) (1 : Rtop)) = (1 : Rtop) at hi
  rw [hPlus, hMinus]
  exact hi.trans ((hr.trans (one_smul Rtop (1 : Rtop))).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldPointCanonicalTwistPairingScalar_eval :
    (Scheme.ΓSpecIso (.of L)).hom
      ((actualFieldPointCanonicalTwistPairingIso I q m).hom.val.app (op ⊤)
        (actualModuleLocalTensorSection ((P).obj Tplus) ((P).obj Tminus) ⊤ n₁ t₁)) =
      actualFieldPointCanonicalTwistPairingScalar I q m := by
  change _ = (Scheme.ΓSpecIso (.of L)).hom
    ((actualFieldPointCanonicalTwistPairingIso I q m).hom.val.app (op ⊤)
      ((actualFieldPointTwistFramesPairUnitIso I q m).inv.val.app (op ⊤) (1 : Rtop)))
  rw [pairedFrames_inverse_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldPointNegativeFrame_eq_fiberEquiv_symm_one :
    t₁ = (actualFieldPointNegativeTwistFiberEquiv I q m).symm 1 := by
  let b := actualFieldPointNegativeTwistFiberEquiv I q m
  apply b.injective
  rw [b.apply_symm_apply]
  rw [actualFieldPointNegativeTwistFiberEquiv_apply]
  have h := congrArg (fun v => (SheafOfModules.Hom.val v).app (op ⊤) (1 : Rtop)) (e₋).inv_hom_id
  change (e₋).hom.val.app (op ⊤) t₁ = (1 : Rtop) at h
  rw [h, map_one]

end
end PfaffianDescent
