import PfaffianDescent.ActualOriginalWholeSourceAugmentationMatch213

/-! SOURCE ONLY218. A bounded point-indexed transport of the complete213
statement, retaining literal original scheme, quotient, and actual maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actualOriginalPoint_sourceAugmentation_unitMatch218
    {X Y : Scheme.{u}} (s : X ⟶ Y) [IsClosedImmersion s] (P : X) [IsClosedImmersion (X.fromSpecResidueField P)]
    (U : X.Opens) (hPU : P ∈ U) (j : Spec (X.residueField P) ⟶ (U : Scheme))
    (hji : j ≫ U.ι = X.fromSpecResidueField P)
    (y : Spec (X.residueField P)) :
    let i := X.fromSpecResidueField P
    let x := P
    let B := X.presheaf.stalk x
    let R := Y.presheaf.stalk (s x)
    let F := schemeModuleStalkModuleFunctor X x
    let H := schemeModuleStalkModuleFunctor Y (s x)
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let χ := closedImmersionModuleToUnit i
    let S := incrementCokernelSequence χ
    let W := S.map F
    let phi := (s.stalkMap x).hom
    let Phi := ModuleCat.restrictScalars phi
    ∀ (hS : S.ShortExact)
      (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
      (e₀ : B ≃ₗ[B] F.obj M) (t : B) (ht : t ∈ B⁰)
      (he₀ : ∀ r, schemeModuleStalkToRingLinearMap χ x (e₀ r) = r * t)
      (hspan : maximalIdeal B = Ideal.span ({t} : Set B))
      (a : W ≅ pointCartierYonedaCoefficientComplex t)
      (ha₂ : a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U ⟨P, hPU⟩ M e e₀).hom)
      (b₁ : (Scheme.Modules.pullback i).obj D ≅
        (show (Spec (X.residueField P)).Modules from
          SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf))
      (E₁ : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (show (Spec (X.residueField P)).Modules from
          SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf))
      (hE₁ : S.g ≫ E₁.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
        (Scheme.Modules.pushforward i).map b₁.hom)
      (f g : R) (eR : (R ⧸ Ideal.span {f}) ≃+* B)
      (hphi : phi = eR.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f}))),
    let qR := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars qR
    let eta := ModuleCat.restrictScalarsComp' qR eR.toRingHom phi hphi
    let aC := quotientWholePrincipalIso202 f eR W t ht a
    let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    ∀ (kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃),
      (localSerreIdealQuotientComplex f g).g ≫ kappa =
        (pointCartierYonedaCoefficientComplex f).g ≫
          ((Q.map e₂.inv ≫ (eta.app W.X₂).inv) ≫ Phi.map W.g) →
    let b₀ : (Scheme.Modules.pullback i).obj D ≅
      (show (Spec (X.residueField P)).Modules from
        SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf) := by
          simpa only [hji] using schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
    let alpha : X.residueField P :=
      actualPointFiberFrameComparisonScalar205 (L := X.residueField P) i D b₀ b₁
    let rho : X.residueField P := residue B (actualOriginalIdealFrameUnit205 U ⟨P, hPU⟩ M e e₀)
    let theta := rho / alpha
    let mu := F.map (E₁.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta ≫ E₁.inv)
    let beta := actualSupportedPointWholeSourceIso213 s i S.X₃ E₁
    let etaM := pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing x S.X₃
    let T := (closedImmersionIdealTwistSequence (i ≫ s)
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃
    let ringSource := (schemeModuleUnitStalkIso Y (s x)).inv ≫
      H.map (closedImmersionUnitToPushforwardUnit (i ≫ s)) ≫
        H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).inv
    IsUnit theta ∧
      ∃ lambda : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ H.obj T,
        (localSerreIdealQuotientComplex f g).g ≫ lambda = ringSource ∧
        lambda ≫ (H.map beta.hom ≫ etaM.hom) = kappa ≫ Phi.map mu ∧ Epi lambda := by
  haveI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  have hImage : j y = (⟨P, hPU⟩ : U) := by
    apply Subtype.ext
    exact (congrArg (fun f => f y) hji).trans (Scheme.fromSpecResidueField_apply P y)
  let nativeStatement (k : Spec (X.residueField P) ⟶ X) (w : U) : Prop :=
    ∀ (hk : IsClosedImmersion k),
    letI := hk
    ∀ (hfac : j ≫ U.ι = k) (hw : U.ι w = P),
        let i := k
        let x := U.ι w
        let B := X.presheaf.stalk x
        let R := Y.presheaf.stalk (s x)
        let F := schemeModuleStalkModuleFunctor X x
        let H := schemeModuleStalkModuleFunctor Y (s x)
        let M := (show X.Modules from closedImmersionModule i)
        let D := dual M
        let χ := closedImmersionModuleToUnit i
        let S := incrementCokernelSequence χ
        let W := S.map F
        let phi := (s.stalkMap x).hom
        let Phi := ModuleCat.restrictScalars phi
        ∀ (hS : S.ShortExact)
          (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
          (e₀ : B ≃ₗ[B] F.obj M) (t : B) (ht : t ∈ B⁰)
          (he₀ : ∀ r, schemeModuleStalkToRingLinearMap χ x (e₀ r) = r * t)
          (hspan : maximalIdeal B = Ideal.span ({t} : Set B))
          (a : W ≅ pointCartierYonedaCoefficientComplex t)
          (ha₂ : a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U w M e e₀).hom)
          (b₁ : (Scheme.Modules.pullback i).obj D ≅
            (show (Spec (X.residueField P)).Modules from
              SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf))
          (E₁ : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
            (show (Spec (X.residueField P)).Modules from
              SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf))
          (hE₁ : S.g ≫ E₁.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
            (Scheme.Modules.pushforward i).map b₁.hom)
          (f g : R) (eR : (R ⧸ Ideal.span {f}) ≃+* B)
          (hphi : phi = eR.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f}))),
        let qR := Ideal.Quotient.mk (Ideal.span {f})
        let Q := ModuleCat.restrictScalars qR
        let eta := ModuleCat.restrictScalarsComp' qR eR.toRingHom phi hphi
        let aC := quotientWholePrincipalIso202 f eR W t ht a
        let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
        ∀ (kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃),
          (localSerreIdealQuotientComplex f g).g ≫ kappa =
            (pointCartierYonedaCoefficientComplex f).g ≫
              ((Q.map e₂.inv ≫ (eta.app W.X₂).inv) ≫ Phi.map W.g) →
        let b₀ : (Scheme.Modules.pullback i).obj D ≅
          (show (Spec (X.residueField P)).Modules from
            SheafOfModules.unit (Spec (X.residueField P)).ringCatSheaf) := by
              simpa only [hfac] using schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
        let alpha : X.residueField P :=
          actualPointFiberFrameComparisonScalar205 (L := X.residueField P) i D b₀ b₁
        let rho : X.residueField P := (X.residueFieldCongr hw).hom
          (residue B (actualOriginalIdealFrameUnit205 U w M e e₀))
        let theta := rho / alpha
        let mu := F.map (E₁.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta ≫ E₁.inv)
        let beta := actualSupportedPointWholeSourceIso213 s i S.X₃ E₁
        let etaM := pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing x S.X₃
        let T := (closedImmersionIdealTwistSequence (i ≫ s)
          (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃
        let ringSource := (schemeModuleUnitStalkIso Y (s x)).inv ≫
          H.map (closedImmersionUnitToPushforwardUnit (i ≫ s)) ≫
            H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).inv
        IsUnit theta ∧
          ∃ lambda : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ H.obj T,
            (localSerreIdealQuotientComplex f g).g ≫ lambda = ringSource ∧
            lambda ≫ (H.map beta.hom ≫ etaM.hom) = kappa ≫ Phi.map mu ∧ Epi lambda
  have hChart : nativeStatement (j ≫ U.ι) (j y) := by
    dsimp only [nativeStatement]
    intro hk hfac hw
    exact actualOriginalWholePoint_sourceAugmentation_unitMatch213 s P U j hji y
  have hOriginalMap : nativeStatement (X.fromSpecResidueField P) (j y) :=
    Eq.mp (congrArg (fun k => nativeStatement k (j y)) hji) hChart
  have hOriginalPoint : nativeStatement (X.fromSpecResidueField P) ⟨P, hPU⟩ :=
    Eq.mp (congrArg (nativeStatement (X.fromSpecResidueField P)) hImage) hOriginalMap
  have hLiteral := hOriginalPoint inferInstance hji rfl
  simpa only [Scheme.Opens.ι_apply, Scheme.residueFieldCongr_refl,
    Iso.refl_hom, CommRingCat.id_apply] using hLiteral

end PfaffianDescent
