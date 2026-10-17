import PfaffianDescent.ActualSupportedPointSourceCoordinate213
import PfaffianDescent.WholePrincipalAugmentationValue213
import PfaffianDescent.ActualWholePointQuotientFrameUnitAssembly209

/-! SOURCE ONLY213. Generic bounded assembly of the ACTUAL original source
augmentation.200/209 supply the whole principal data,203 the global E,196 the
literal quotient chart, and202 its defining augmentation projection. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual canonical surface restriction factors through the whole
pair quotient. Its derived augmentation matches210's SOURCE coordinate and
202's SAME whole local augmentation, up to209's internally derived unit.
All input equations are ordinary earlier construction data; neither the
source comparison, its scalar, nor any nonzero class is a premise. -/
theorem actualOriginalWholePoint_sourceAugmentation_unitMatch213
    {X Y : Scheme.{u}} (s : X ⟶ Y) [IsClosedImmersion s] (P : X)
    (U : X.Opens) (j : Spec (X.residueField P) ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (hji : j ≫ U.ι = X.fromSpecResidueField P)
    (y : Spec (X.residueField P)) :
    let i := j ≫ U.ι
    let x := i y
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
      (ha₂ : a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U (j y) M e e₀).hom)
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
    let hp : x = P := (congrArg (fun v => v y) hji).trans (Scheme.fromSpecResidueField_apply P y)
    let b₀ := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
    let alpha : X.residueField P :=
      actualPointFiberFrameComparisonScalar205 (L := X.residueField P) i D b₀ b₁
    let rho := (X.residueFieldCongr hp).hom
      (residue B (actualOriginalIdealFrameUnit205 U (j y) M e e₀))
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
  dsimp only
  intro hS e e₀ t ht he₀ hspan a ha₂ b₁ E₁ hE₁ f g eR hphi kappa hProjection
  let i := j ≫ U.ι
  let x := i y
  let B := X.presheaf.stalk x
  let R := Y.presheaf.stalk (s x)
  let F := schemeModuleStalkModuleFunctor X x
  let H := schemeModuleStalkModuleFunctor Y (s x)
  let M := (show X.Modules from closedImmersionModule i)
  let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let W := S.map F
  let Phi := ModuleCat.restrictScalars (s.stalkMap x).hom
  let q := (ShortComplex.π₃ : ShortComplex (ModuleCat B) ⥤ _).mapIso a
  have hq : W.g ≫ q.hom =
      (actualDualIncrementStalkCoefficientIso194 U (j y) M e e₀).hom ≫
        (pointCartierYonedaCoefficientComplex t).g := by
    exact a.hom.comm₂₃.symm.trans (congrArg (fun v => v ≫
      (pointCartierYonedaCoefficientComplex t).g) ha₂)
  let hp : x = P := (congrArg (fun v => v y) hji).trans (Scheme.fromSpecResidueField_apply P y)
  let k := (X.residueFieldCongr hp).commRingCatIsoToRingEquiv
  let b₀ := schemeModuleFiberFrameIso U.ι j (dual M) (dualRestrictUnitIso U e)
  let alpha : X.residueField P :=
    actualPointFiberFrameComparisonScalar205 (L := X.residueField P) i (dual M) b₀ b₁
  have hTotal :
      IsUnit ((closedFieldPointResidueRingEquivAt (L := X.residueField P) i y
        (residue B (actualOriginalIdealFrameUnit205 U (j y) M e e₀))) / alpha) ∧
      ∀ z : W.X₃,
        closedFieldPointResidueRingEquivAt (L := X.residueField P) i y
            (actualPointParameterResidueLinearEquiv194 t hspan (q.hom z)) =
          ((closedFieldPointResidueRingEquivAt (L := X.residueField P) i y
            (residue B (actualOriginalIdealFrameUnit205 U (j y) M e e₀))) / alpha) *
              actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y
                ((F.map E₁.hom) z) :=
    actualWholePointQuotient_totalResidueUnit209 (L := X.residueField P) U j y M e
      (closedImmersionModuleToUnit i) hS e₀ t he₀ hspan q hq b₁ E₁ hE₁
  have hOriginal : closedFieldPointResidueRingEquivAt (L := X.residueField P) i y = k :=
    actualOriginalResiduePointCoordinate_eq207 P i hji y
  rw [hOriginal] at hTotal
  let rho := k (residue B (actualOriginalIdealFrameUnit205 U (j y) M e e₀))
  let theta := rho / alpha
  let muSheaf := E₁.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta ≫ E₁.inv
  let mu := F.map muSheaf
  let coord : W.X₃ → X.residueField P := fun z =>
    k (actualPointParameterResidueLinearEquiv194 t hspan (q.hom z))
  have hCoord (z : W.X₃) : coord z = theta *
      actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y ((F.map E₁.hom) z) := hTotal.2 z
  have hInjective : Function.Injective coord :=
    k.injective.comp ((actualPointParameterResidueLinearEquiv194 t hspan).injective.comp
      (ConcreteCategory.bijective_of_isIso q.hom).injective)
  have hMuSquare : muSheaf ≫ E₁.hom =
      E₁.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta := by
    simp only [muSheaf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hMuNative : mu ≫ F.map E₁.hom =
      F.map E₁.hom ≫ F.map (fieldPointPushforwardScalarEndomorphismAddHom
        (L := X.residueField P) i theta) :=
    (F.map_comp muSheaf E₁.hom).symm.trans
      ((congrArg F.map hMuSquare).trans
        (F.map_comp E₁.hom
          (fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta)))
  have hMuCoord (z : W.X₃) : coord (mu z) = theta * coord z := by
    have hv := ConcreteCategory.congr_hom hMuNative z
    have hs := fieldPointPushforwardScalarEndomorphism_stalk_coordinate (L := X.residueField P) i y theta
      ((F.map E₁.hom) z)
    change actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y
        ((F.map (fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta)) ((F.map E₁.hom) z)) =
      theta * actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y ((F.map E₁.hom) z) at hs
    change (F.map E₁.hom) (mu z) =
      (F.map (fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P) i theta)) ((F.map E₁.hom) z) at hv
    rw [hCoord (mu z), hv, hs, hCoord z]
  let beta := actualSupportedPointWholeSourceIso213 s i S.X₃ E₁
  let etaM := pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing x S.X₃
  let K := H.mapIso beta ≪≫ etaM
  let T := (closedImmersionIdealTwistSequence (i ≫ s)
    (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃
  let ringSource : ModuleCat.of R R ⟶ H.obj T :=
    (schemeModuleUnitStalkIso Y (s x)).inv ≫
      H.map (closedImmersionUnitToPushforwardUnit (i ≫ s)) ≫
        H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).inv
  have hCanonicalValue (r : R) :
      actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y
        ((F.map E₁.hom) (K.hom (ringSource r))) = k (residue B (s.stalkMap x r)) := by
    have h : actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P) i y
        ((F.map E₁.hom) (K.hom (ringSource r))) =
          closedFieldPointResidueRingEquivAt (L := X.residueField P) i y
            (X.residue x (s.stalkMap x r)) :=
      actualSupportedPointWholeSource_ringCoordinate213 (L := X.residueField P) s i y S.X₃ E₁ r
    rw [hOriginal] at h
    exact h
  have hKappaValue (r : R) : coord
      (kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r)) = k (residue B (s.stalkMap x r)) := by
    have h := wholeOriginalRestrictionAugmentation_principalValue213 f g eR
      (s.stalkMap x).hom hphi W t ht a kappa hProjection r
    change q.hom (kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r)) =
      Ideal.Quotient.mk (Ideal.span ({t} : Set B)) (s.stalkMap x r) at h
    change k (actualPointParameterResidueLinearEquiv194 t hspan
      (q.hom (kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r)))) = _
    rw [h, actualPointParameterResidueLinearEquiv_mk194]
  have hLift : ringSource ≫ K.hom =
      (localSerreIdealQuotientComplex f g).g ≫ kappa ≫ Phi.map mu := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    apply hInjective
    change coord (K.hom (ringSource r)) =
      coord (mu (kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r)))
    rw [hCoord, hCanonicalValue, hMuCoord, hKappaValue]
  let lambda := kappa ≫ Phi.map mu ≫ K.inv
  have hFactor : (localSerreIdealQuotientComplex f g).g ≫ lambda = ringSource := by
    simpa only [lambda, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z => z ≫ K.inv) hLift.symm
  have hMatch : lambda ≫ K.hom = kappa ≫ Phi.map mu := by
    simp only [lambda, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hRingSurjective : Function.Surjective ringSource := by
    intro z
    obtain ⟨r, hr⟩ := closedImmersionPushforwardStalkFromRingLinearMap_surjective
      (i ≫ s) (s x) ((H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).hom) z)
    refine ⟨r, ?_⟩
    change (H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).inv)
      (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ s) (s x) r) = z
    rw [hr]
    exact ConcreteCategory.congr_hom
      (H.mapIso (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s))).hom_inv_id z
  have hEpi : Epi lambda := by
    apply (ModuleCat.epi_iff_surjective lambda).mpr
    intro z
    obtain ⟨r, hr⟩ := hRingSurjective z
    refine ⟨(localSerreIdealQuotientComplex f g).g r, ?_⟩
    exact (ConcreteCategory.congr_hom hFactor r).trans hr
  exact ⟨hTotal.1, lambda, hFactor, hMatch, hEpi⟩

end PfaffianDescent
