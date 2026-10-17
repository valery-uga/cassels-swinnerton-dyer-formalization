import PfaffianDescent.ActualOriginalPointWholeWitness218
import PfaffianDescent.ActualOriginalPointSourceAugmentation218
import PfaffianDescent.OriginalSurfaceTargetQuotientCoordinate212
import PfaffianDescent.WholeOriginalRestrictionCoefficient202

/-! SOURCE ONLY218. The literal original curve/closed point constructs the
entire200/209 witness, genuine196 quotient,202 augmentation, and canonical
213 source factorization together. The SAME a/E/kappa remain available. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- This names the complete constructed data, including the actual whole
projection and coefficient-one class, without concealing comparison premises. -/
def originalCurvePointSurfaceSourceData218
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (eX : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (P : closedPoints X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (eX.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) : Prop :=
    let Y := hypersurface p hp
    let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let B := X.presheaf.stalk P.1
    let R := Y.presheaf.stalk (s P.1)
    let F := schemeModuleStalkModuleFunctor X P.1
    let H := schemeModuleStalkModuleFunctor Y (s P.1)
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let chi := closedImmersionModuleToUnit i
    let S := incrementCokernelSequence chi
    let W := S.map F
    let phi := (s.stalkMap P.1).hom
    let Phi := ModuleCat.restrictScalars phi
    let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
    let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
    let eR := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X eX P.1 j hx
    let hphi := originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X eX P.1 j hx
    let qR := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars qR
    let eta := ModuleCat.restrictScalarsComp' qR eR.toRingHom phi hphi
    ∃ hS : S.ShortExact,
    ∃ (U : X.Opens) (hPU : P.1 ∈ U)
      (jP : Spec (X.residueField P.1) ⟶ (U : Scheme)) (hji : jP ≫ U.ι = i),
    ∃ e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U,
    ∃ (t : B) (e0 : B ≃ₗ[B] F.obj M)
      (hspan : maximalIdeal B = Ideal.span ({t} : Set B)) (ht : t ∈ B⁰),
      (∀ r, schemeModuleStalkToRingLinearMap chi P.1 (e0 r) = r * t) ∧
    ∃ a : W ≅ pointCartierYonedaCoefficientComplex t,
      a.hom.τ₁ = (schemeModuleUnitStalkIso X P.1).hom ∧
      a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U ⟨P.1, hPU⟩ M e e0).hom ∧
    ∃ (b : (Scheme.Modules.pullback i).obj D ≅
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
      S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
        (Scheme.Modules.pushforward i).map b.hom ∧
    let aC := quotientWholePrincipalIso202 f eR W t ht a
    let e1 := (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    let e2 := (ShortComplex.π₂ : ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    let b0 : (Scheme.Modules.pullback i).obj D ≅
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf) := by
          simpa only [hji] using schemeModuleFiberFrameIso U.ι jP D (dualRestrictUnitIso U e)
    let alpha : X.residueField P.1 :=
      actualPointFiberFrameComparisonScalar205 (L := X.residueField P.1) i D b0 b
    let rho : X.residueField P.1 := residue B (actualOriginalIdealFrameUnit205 U ⟨P.1, hPU⟩ M e e0)
    let theta := rho / alpha
    let mu := F.map (E.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (L := X.residueField P.1) i theta ≫ E.inv)
    let beta := actualSupportedPointWholeSourceIso213 s i S.X₃ E
    let etaM := pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing P.1 S.X₃
    let T := (closedImmersionIdealTwistSequence (i ≫ s)
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃
    let ringSource := (schemeModuleUnitStalkIso Y (s P.1)).inv ≫
      H.map (closedImmersionUnitToPushforwardUnit (i ≫ s)) ≫
        H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)).inv
    ∀ (hExtR : HasExt.{u + 1} (ModuleCat.{u} R))
      (hExtC : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {f}))),
    letI := hExtR
    letI := hExtC
    ∃ (g : R) (hgt : phi g = t) (hg : qR g ∈ (R ⧸ Ideal.span {f})⁰)
      (kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃),
      (localSerreIdealQuotientComplex f g).g ≫ kappa =
        (pointCartierYonedaCoefficientComplex f).g ≫
          ((Q.map e2.inv ≫ (eta.app W.X₂).inv) ≫ Phi.map W.g) ∧
      ((Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) kappa).comp
          ((ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} R)
              ((hS.map_of_exact F).map_of_exact Phi)).comp
            (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) ((eta.app W.X₁).hom ≫ Q.map e1.hom)) (add_zero 1))
          (zero_add 1)).comp
        (ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} R)
          (pointCartierYonedaCoefficientComplex_shortExact f hf)) rfl =
          (@localSerreExtTwoClass.{u, u + 1} R inferInstance f g 1 hf hg hExtR) ∧
      (@localSerreExtTwoClass.{u, u + 1} R inferInstance f g 1 hf hg hExtR) ≠ 0 ∧
      IsUnit theta ∧
      ∃ lambda : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ H.obj T,
        (localSerreIdealQuotientComplex f g).g ≫ lambda = ringSource ∧
        lambda ≫ (H.map beta.hom ≫ etaM.hom) = kappa ≫ Phi.map mu ∧ Epi lambda

/-- Genuine original geometry constructs every comparison input internally.
The same witnessed a/E/kappa is retained for the actual217 class assembly. -/
theorem originalCurvePoint_exists_surfaceSourceUnitMatch218
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (eX : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (eX.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    originalCurvePointSurfaceSourceData218 p l hp hp0 hl hl0 X eX P j hx := by
  classical
  let Y := hypersurface p hp
  let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let B := X.presheaf.stalk P.1
  let R := Y.presheaf.stalk (s P.1)
  let F := schemeModuleStalkModuleFunctor X P.1
  let M := (show X.Modules from closedImmersionModule i)
  let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let W := S.map F
  let phi := (s.stalkMap P.1).hom
  let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
  let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
  let eR := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X eX P.1 j hx
  let hphi := originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X eX P.1 j hx
  obtain ⟨hS, U, hPU, jP, hji, e, t, e0, hspan, ht, he0,
    a, ha1, ha2, b, E, hE⟩ := actualOriginalClosedPoint_exists_literalWholeWitness218 X P
  refine ⟨hS, U, hPU, jP, hji, e, t, e0, hspan, ht, he0,
    a, ha1, ha2, b, E, hE, ?_⟩
  dsimp only
  intro hExtR hExtC
  letI := hExtR
  letI := hExtC
  have hmem : t ∈ maximalIdeal B := by
    rw [hspan]
    exact Ideal.subset_span (by simp)
  obtain ⟨g, hgt, hg, kappa, hProjection, hClass, hLocalNonzero⟩ :=
    @wholePoint_originalRestriction_firstCartier_coefficientOne202.{u, u + 1, u + 1}
      R B inferInstance inferInstance inferInstance hExtR f hExtC hf eR phi hphi
      W (hS.map_of_exact F) t ht hmem a
  have hMatch := actualOriginalPoint_sourceAugmentation_unitMatch218 s P.1 U hPU
    jP hji (default : Spec (X.residueField P.1)) hS e e0 t ht he0 hspan
    a ha2 b E hE f g eR hphi kappa hProjection
  exact ⟨g, hgt, hg, kappa, hProjection, hClass, hLocalNonzero, hMatch.1, hMatch.2⟩

end PfaffianDescent.Coray
