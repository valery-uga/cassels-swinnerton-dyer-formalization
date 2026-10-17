import PfaffianDescent.ActualNegativeTwistPullbackTensorIso
import PfaffianDescent.ActualModuleLocalTensorInverseContraction
import PfaffianDescent.ActualFieldPointNegativeTwistUnitIso
import PfaffianDescent.ActualFieldPointPullbackNestedTensorMapExt
import PfaffianDescent.ActualPointLocalSectionClassScalar

/-! SOURCE ONLY / UNVERIFIED. FULL actual point pullback contraction
coherence is derived from the genuine local tensor formulas and both
adjunctions. No supplied desired comparison premise appears. -/
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
local notation "Tplus" => positiveSheafOfModules (grading I) m
local notation "Tminus" => sheafOfModules (grading I) m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical point pairing, with its inverse tensor comparison
internally derived and its original pullback-unit coefficient map. -/
def actualFieldPointCanonicalTwistPairingIso :
    schemeModuleTensor ((P).obj Tplus) ((P).obj Tminus) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf := by
  letI : IsIso (pullbackUnitComparison q) := isIso_pullbackUnitComparison q
  exact (actualNegativeTwistPullbackTensorIso I q Tplus m).symm ≪≫
    (P).mapIso (quotientPositiveNegativeTensorInverseIso_all I m) ≪≫
      (@asIso _ _ _ _ (pullbackUnitComparison q) (isIso_pullbackUnitComparison q))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldPointCanonicalTwistPairingIso_localPure
    (U : (scheme I).Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (n : (Tplus).val.obj (op U)) (t : (Tminus).val.obj (op U)) :
    (actualFieldPointCanonicalTwistPairingIso I q m).hom.val.app (op ⊤)
      (actualModuleLocalTensorSection ((P).obj Tplus) ((P).obj Tminus) ⊤
        (actualPointLocalSectionClass q Tplus U hU n)
        (actualPointLocalSectionClass q Tminus U hU t)) =
    (pullbackUnitComparison q).val.app (op ⊤)
      (actualPointLocalSectionClass q (SheafOfModules.unit (scheme I).ringCatSheaf) U hU
        ((quotientPositiveNegativeTensorInverseIso_all I m).hom.val.app (op U)
          (actualModuleLocalTensorSection Tplus Tminus U n t))) := by
  let c := actualNegativeTwistPullbackTensorIso I q Tplus m
  let e := quotientPositiveNegativeTensorInverseIso_all I m
  let ep := actualFieldPointCanonicalTwistPairingIso I q m
  let u := pullbackUnitComparison q
  let z := actualPointLocalSectionClass q (schemeModuleTensor Tplus Tminus) U hU
    (actualModuleLocalTensorSection Tplus Tminus U n t)
  have hc := actualPointLocalTensorPullbackAction q Tplus Tminus U hU n t
  have hn := actualPointLocalSectionClass_naturality q e.hom U hU
    (actualModuleLocalTensorSection Tplus Tminus U n t)
  have hcancel : c.hom ≫ ep.hom = (P).map e.hom ≫ u := by
    simp only [c, e, u, ep, actualFieldPointCanonicalTwistPairingIso, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, asIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
  have heval := congrArg (fun v => (G).map v z) hcancel
  simp only [Functor.map_comp, ModuleCat.comp_apply] at heval
  exact (congrArg ((G).map ep.hom) hc.symm).trans
    (heval.trans (congrArg ((G).map u) hn))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ACTUAL full-fiber contraction square, not merely its local
pure-section instance. The local detection lemma internally proves that
its test sections suffice. -/
theorem actualFieldPointCanonicalTwistContraction_pullback
    (M : (scheme I).Modules) :
    letI := quotientNegativeTwistComparison_isIso_all I m
      (PresheafOfModules.Monoidal.tensorObj M.val (Tplus).val)
    letI := schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
      (PresheafOfModules.Monoidal.tensorObj ((P).obj M).val ((P).obj Tplus).val)
      (actualFieldPointNegativeTwistUnitIso I q m)
    (P).map (schemeModuleTensorContraction M Tplus Tminus
        (quotientPositiveNegativeTensorInverseIso_all I m)) =
      (actualNegativeTwistPullbackTensorIso I q (schemeModuleTensor M Tplus) m).hom ≫
      schemeModuleTensorMap (actualPositiveTwistPullbackTensorIso I q M m).hom
        (𝟙 ((P).obj Tminus)) ≫
      schemeModuleTensorContraction ((P).obj M) ((P).obj Tplus) ((P).obj Tminus)
        (actualFieldPointCanonicalTwistPairingIso I q m) := by
  letI := quotientNegativeTwistComparison_isIso_all I m
    (PresheafOfModules.Monoidal.tensorObj M.val (Tplus).val)
  letI := schemeModuleTensorSheafificationRightComparison_isIso_of_iso_unit
    (PresheafOfModules.Monoidal.tensorObj ((P).obj M).val ((P).obj Tplus).val)
    (actualFieldPointNegativeTwistUnitIso I q m)
  let A := schemeModuleTensor M Tplus
  let cNeg := actualNegativeTwistPullbackTensorIso I q A m
  let cPos := actualPositiveTwistPullbackTensorIso I q M m
  let e := quotientPositiveNegativeTensorInverseIso_all I m
  let ep := actualFieldPointCanonicalTwistPairingIso I q m
  let D := schemeModuleTensorContraction M Tplus Tminus e
  let Dp := schemeModuleTensorContraction ((P).obj M) ((P).obj Tplus) ((P).obj Tminus) ep
  apply actualFieldPointPullbackNestedTensorMap_ext q M Tplus Tminus ((P).obj M)
    ((P).map D) (cNeg.hom ≫ schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp)
  intro U hU w n t
  let wq : Γ((P).obj M, ⊤) := actualPointLocalSectionClass q M U hU w
  let nq := actualPointLocalSectionClass q Tplus U hU n
  let tq := actualPointLocalSectionClass q Tminus U hU t
  let r : Γ(scheme I, U) :=
    e.hom.val.app (op U) (actualModuleLocalTensorSection Tplus Tminus U n t)
  let rq : Γ(Spec (.of L), ⊤) := (pullbackUnitComparison q).val.app (op ⊤)
    (actualPointLocalSectionClass q (SheafOfModules.unit (scheme I).ringCatSheaf) U hU r)
  have hn := actualPointLocalSectionClass_naturality q D U hU
    (actualModuleLocalTensorSection A Tminus U (actualModuleLocalTensorSection M Tplus U w n) t)
  have hg := actualModuleLocalTensorInverseContraction M Tplus Tminus e U w n t
  have hs := actualPointLocalSectionClass_scalar q M U hU r w
  have hleft : (G).map ((P).map D)
      (actualPointLocalSectionClass q (schemeModuleTensor A Tminus) U hU
        (actualModuleLocalTensorSection A Tminus U
          (actualModuleLocalTensorSection M Tplus U w n) t)) = rq • wq :=
    hn.trans ((congrArg (actualPointLocalSectionClass q M U hU) hg).trans hs)
  have hcNeg := actualPointLocalTensorPullbackAction q A Tminus U hU
    (actualModuleLocalTensorSection M Tplus U w n) t
  have hcPos := actualPointLocalTensorPullbackAction q M Tplus U hU w n
  have ht := actualModuleLocalTensorSection_naturality cPos.hom
    (𝟙 ((P).obj Tminus)) ⊤
    (actualPointLocalSectionClass q A U hU
      (actualModuleLocalTensorSection M Tplus U w n)) tq
  have hd := actualModuleLocalTensorInverseContraction
    ((P).obj M) ((P).obj Tplus) ((P).obj Tminus) ep ⊤ wq nq tq
  have hp := actualFieldPointCanonicalTwistPairingIso_localPure I q m U hU n t
  have hright : (G).map
      (cNeg.hom ≫ schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)) ≫ Dp)
      (actualPointLocalSectionClass q (schemeModuleTensor A Tminus) U hU
        (actualModuleLocalTensorSection A Tminus U
          (actualModuleLocalTensorSection M Tplus U w n) t)) = rq • wq := by
    simp only [Functor.map_comp, ModuleCat.comp_apply]
    have hcNeg' : (G).map cNeg.hom
        (actualPointLocalSectionClass q (schemeModuleTensor A Tminus) U hU
          (actualModuleLocalTensorSection A Tminus U
            (actualModuleLocalTensorSection M Tplus U w n) t)) =
        actualModuleLocalTensorSection ((P).obj A) ((P).obj Tminus) ⊤
          (actualPointLocalSectionClass q A U hU
            (actualModuleLocalTensorSection M Tplus U w n)) tq := hcNeg
    have hcPos' : cPos.hom.val.app (op ⊤)
        (actualPointLocalSectionClass q A U hU
          (actualModuleLocalTensorSection M Tplus U w n)) =
        actualModuleLocalTensorSection ((P).obj M) ((P).obj Tplus) ⊤ wq nq := hcPos
    have hid : (SheafOfModules.Hom.val (𝟙 ((P).obj Tminus))).app (op ⊤) tq = tq := rfl
    have hmiddle : (G).map
        (schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus)))
        (actualModuleLocalTensorSection ((P).obj A) ((P).obj Tminus) ⊤
          (actualPointLocalSectionClass q A U hU
            (actualModuleLocalTensorSection M Tplus U w n)) tq) =
        actualModuleLocalTensorSection
          (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤
          (actualModuleLocalTensorSection ((P).obj M) ((P).obj Tplus) ⊤ wq nq) tq :=
      ht.trans (congrArg₂
        (fun (x : Γ(schemeModuleTensor ((P).obj M) ((P).obj Tplus), ⊤))
          (y : Γ((P).obj Tminus, ⊤)) =>
          actualModuleLocalTensorSection
            (schemeModuleTensor ((P).obj M) ((P).obj Tplus)) ((P).obj Tminus) ⊤ x y)
        hcPos' hid)
    exact (congrArg
      (fun x : Γ(schemeModuleTensor ((P).obj A) ((P).obj Tminus), ⊤) =>
        (G).map Dp ((G).map
          (schemeModuleTensorMap cPos.hom (𝟙 ((P).obj Tminus))) x)) hcNeg').trans
      ((congrArg ((G).map Dp) hmiddle).trans
        (hd.trans (congrArg (fun a : Γ(Spec (.of L), ⊤) => a • wq) hp)))
  exact hleft.trans hright.symm

end
end PfaffianDescent
