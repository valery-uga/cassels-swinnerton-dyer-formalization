import PfaffianDescent.CorayCartierIntrinsicNormalCechH1
import PfaffianDescent.CorayPushforwardCechAugmentationUnit
import PfaffianDescent.SchemeCoverDegreeOneBoundaryLift
import PfaffianDescent.ClosedImmersionCohomologyOneBoundary

/-! Canonical exact-right-adjoint Ext compatibility for the SAME actual
Cartier coefficient and the SAME original Cech transport. Every class is
an actual intrinsic injective-presentation boundary; original coefficient,
differential and normalized-augmentation squares identify its transported
cover class with the canonical ambient connecting class. No desired
compatibility, lift, QC or vanishing input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Ext.subsingleton_of_injective

/-- The actual Cech comparison composed with the ORIGINAL canonical
closed-immersion Ext map is identity. OWN coefficient QC and cover Ext1
vanishing, actual lift existence and augmentation/unit compatibility are
all derived internally, with original K actions unchanged. -/
theorem RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv_canonical
    (pi : X ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ X) [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules] :
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
    letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
    ∀ a : schemeModuleCohomology Y D 1,
      PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW
        (closedImmersion_cohomologyOneLinearMap pi i D a) = a := by
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
  letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
  letI : EnoughInjectives Y.Modules := sheafOfModules_enoughInjectives Y.ringCatSheaf
  have hQC := H.actualIntrinsicNormalCoefficient_and_pushforward_isQuasicoherent W hW
  letI : D.IsQuasicoherent := hQC.1
  let U : X.affineOpens → X.Opens := fun a => a.1
  let V : X.affineOpens → Y.Opens := fun a => i ⁻¹ᵁ a.1
  let hU := genericNormalization_affineOpenFamily_coversTop X
  let hV := schemeModulePushforward_preimageFamily_coversTop i U hU
  let G := Scheme.Modules.pushforward i
  letI : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (SheafOfModules.pushforward i.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  letI : ∀ a, Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from sectionRepresenter Y.ringCatSheaf (V a)) D 1) := fun a =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen
      (V a) (a.2.preimage i) D).1
  letI : Subsingleton (Ext.{u} (C := Y.Modules)
      (show Y.Modules from (sectionRepresenterCechChain Y.ringCatSheaf V).X 0) D 1) :=
    schemeCover_degree_zero_ext_one_subsingleton V D
  let E := PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW
  change ∀ a : schemeModuleCohomology Y D 1,
    E (closedImmersion_cohomologyOneLinearMap pi i D a) = a
  intro a
  let I : InjectivePresentation D := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have ha : a.comp (Ext.mk₀ (C := Y.Modules) S.f) (add_zero 1) = 0 := Subsingleton.elim _ _
  obtain ⟨qExt, hqExt⟩ := Ext.covariant_sequence_exact₁
    (SheafOfModules.unit Y.ringCatSheaf) hS a ha rfl
  let q : SheafOfModules.unit Y.ringCatSheaf ⟶ S.X₃ := Ext.addEquiv₀ qExt
  have hqa : (Ext.mk₀ (C := Y.Modules) q).comp hS.extClass (zero_add 1) = a := by
    rw [Ext.mk₀_addEquiv₀_apply]
    exact hqExt
  obtain ⟨p, z, hp, hz⟩ := schemeCoverDegreeOne_exists_boundary_lift V S hS q
  let pX := (schemeModulePushforwardCechHomAddEquiv i S.X₂ U 0).symm p
  let zX := (schemeModulePushforwardCechOneCocycleAddEquiv i D U).symm z
  let qX := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom ≫ G.map q
  have hpX : pX ≫ (S.map G).g =
      sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
        (schemeCoverCechTargetIsoUnit U).hom ≫ qX := by
    let EQ := schemeModulePushforwardCechHomAddEquiv i S.X₃ U 0
    let EP := schemeModulePushforwardCechHomAddEquiv i S.X₂ U 0
    let C₀ : Y.Modules := (sectionRepresenterCechChain Y.ringCatSheaf V).X 0
    have hleft : EQ (pX ≫ (S.map G).g) = p ≫ S.g :=
      (schemeModulePushforwardCechHomAddEquiv_postcomp i S.X₂ S.X₃ U 0 pX S.g).trans
        (congrArg (fun k : C₀ ⟶ S.X₂ => k ≫ S.g) (EP.apply_symm_apply p))
    have hright : EQ
        (sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop ≫
          (schemeCoverCechTargetIsoUnit U).hom ≫ qX) =
        sectionRepresenterCechAugmentation Y.ringCatSheaf V ⊤ isTerminalTop ≫
          (schemeCoverCechTargetIsoUnit V).hom ≫ q :=
      schemeModulePushforwardCechHomAddEquiv_normalizedAugmentation i S.X₃ U q
    apply EQ.injective
    exact hleft.trans (hp.trans hright.symm)
  have hzX : (sectionRepresenterCechChain X.ringCatSheaf U).d 1 0 ≫ pX =
      zX.1 ≫ (S.map G).f :=
    schemeModulePushforwardCech_degreeOneLiftEquation i D S.X₂ S.f U p z hz
  have hBY := schemeCoverDegreeOneToCohomology_eq_boundary_of_lift V hV S hS q p z hp hz
  have hBX := schemeCoverDegreeOneToCohomology_eq_boundary_of_lift U hU (S.map G)
    (hS.map_of_exact G) qX pX zX hpX hzX
  have hcanonical := closedImmersion_cohomologyOneLinearMap_boundary pi i S hS q
  have hX : (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp
      (schemeCoverDegreeOneToExtHom U hU (G.obj D) zX) (zero_add 1) =
      closedImmersion_cohomologyOneLinearMap pi i D a :=
    hBX.trans (hcanonical.symm.trans
      (congrArg (fun t => closedImmersion_cohomologyOneLinearMap pi i D t) hqa))
  have hY : (Ext.mk₀ (C := Y.Modules) (schemeCoverCechTargetIsoUnit V).inv).comp
      (schemeCoverDegreeOneToExtHom V hV D
        (schemeModulePushforwardCechOneCocycleAddEquiv i D U zX)) (zero_add 1) = a := by
    rw [AddEquiv.apply_symm_apply]
    exact hBY.trans hqa
  have hrep := PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv_representative
    pi i H W hW zX
  exact (congrArg E hX).symm.trans (hrep.trans hY)

/-- Equality of the SAME actual inverse Cech linear equivalence with the
canonical ORIGINAL-K closed-immersion right-adjoint Ext linear map. -/
theorem RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv_symm_eq_canonical
    (pi : X ⟶ Spec (CommRingCat.of K)) (i : Y ⟶ X) [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules] :
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
    letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
    (PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW).symm.toLinearMap =
      closedImmersion_cohomologyOneLinearMap pi i D := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
  letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (i ≫ pi)
  let E := PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW
  ext a
  apply E.injective
  exact (E.apply_symm_apply a).trans
    (PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv_canonical pi i H W hW a).symm

end PfaffianDescent.Coray
end
