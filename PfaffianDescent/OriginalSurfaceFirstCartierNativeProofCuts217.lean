import PfaffianDescent.SupportedWholeAugmentation217
import PfaffianDescent.OriginalCurvePointSurfaceFirstCartier210
import PfaffianDescent.OriginalCurvePointSurfaceDegreeOneClassLargeExt217
import PfaffianDescent.OriginalSurfaceTargetQuotientCoordinate212

/-! The actual210 surface class has the original whole point coefficient
expression after an honestly constructed endpoint pullback. No class match
or nonzero assertion is supplied as an assumption. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule SchemeModuleInternalHom
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-! Genuine native proof cuts; no endpoint/class identity is a premise. -/

theorem originalSurfaceDegreeOne_wholeCoefficient_cut217
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [hExtOriginalCurve : HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    [hExtOriginalSurface : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))))] :
    let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) :=
      hExtOriginalSurface
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
    let F := schemeModuleStalkModuleFunctor X x
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) := S.map F
    let s := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
    let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
    let Q := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {s}))
    let eta := ModuleCat.restrictScalarsComp' (Ideal.Quotient.mk (Ideal.span {s}))
      eQ.toRingHom (f.stalkMap x).hom
        (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
    let beta :
        (closedImmersionIdealTwistSequence (i ≫ f)
          (show (hypersurface p hp).Modules from
            SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃ ≅
        (Scheme.Modules.pushforward f).obj S.X₃ :=
      originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
    let etaM : H.obj ((Scheme.Modules.pushforward f).obj S.X₃) ≅ Phi.obj W.X₃ :=
      pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
    let Kwhole := Iso.trans
      (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
      (H.mapIso beta) etaM
    let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let hs := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom x) j hx
    ∀ (t : X.presheaf.stalk x) (ht : t ∈ (X.presheaf.stalk x)⁰)
      (a : W ≅ pointCartierYonedaCoefficientComplex t)
      (ha₁ : a.hom.τ₁ = (schemeModuleUnitStalkIso X x).hom),
    let aC := quotientWholePrincipalIso202 s eQ W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} _) ⥤ _).mapIso aC
    ((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) a196.hom.τ₃) (add_zero 1) =
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) Kwhole.hom).comp
        ((ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
            ((hS.map_of_exact F).map_of_exact Phi)).comp
          (Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) ((eta.app W.X₁).hom ≫ Q.map e₁.hom)) (add_zero 1)) (zero_add 1) := by
  dsimp only
  let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) :=
    hExtOriginalSurface
  let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
  let F := schemeModuleStalkModuleFunctor X x
  let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
  let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) := S.map F
  let s := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
  let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
  let Q := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {s}))
  let eta := ModuleCat.restrictScalarsComp' (Ideal.Quotient.mk (Ideal.span {s}))
    eQ.toRingHom (f.stalkMap x).hom
      (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
  let beta :
      (closedImmersionIdealTwistSequence (i ≫ f)
        (show (hypersurface p hp).Modules from
          SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward f).obj S.X₃ :=
    originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
  let etaM : H.obj ((Scheme.Modules.pushforward f).obj S.X₃) ≅ Phi.obj W.X₃ :=
    pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
  let Kwhole := Iso.trans
    (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
    (H.mapIso beta) etaM
  let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
  let hs := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom x) j hx
  let R := (hypersurface p hp).presheaf.stalk (f x)
  intro t ht a ha₁
  let aC := quotientWholePrincipalIso202 s eQ W t ht a
  let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} _) ⥤ _).mapIso aC
  let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₁
  let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
  let alphaOld : Ext.{u + 1} (C := ModuleCat.{u} R) (Phi.obj W.X₃) (Phi.obj W.X₁) 1 :=
    (ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} (X.presheaf.stalk x))
      (hS.map_of_exact F)).mapExactFunctor Phi
  let alpha : Ext.{u + 1} (C := ModuleCat.{u} R) (Phi.obj W.X₃) (Phi.obj W.X₁) 1 :=
    ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} R)
      ((hS.map_of_exact F).map_of_exact Phi)
  let bOld : Phi.obj W.X₁ ⟶ (pointCartierYonedaCoefficientComplex s).X₃ :=
    etaN.inv ≫ H.map v.hom ≫ a196.hom.τ₃
  let bNew : Phi.obj W.X₁ ⟶ (pointCartierYonedaCoefficientComplex s).X₃ :=
    (eta.app W.X₁).hom ≫ Q.map e₁.hom
  have hTargetRaw := originalSurfaceTarget_wholeFirstCoordinate212 p l hp hp0 hl hl0 X e x j hx
    W t ht a rfl (by simpa only [eqToHom_refl, Category.id_comp] using ha₁)
  simp only [eqToHom_refl] at hTargetRaw
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hTargetRaw
  have hTarget : bOld = bNew := hTargetRaw
  have hClass : alphaOld = alpha := by
    dsimp only [alphaOld, alpha]
    erw [Ext.mapExactFunctor_extClass]
  have hDegree :
      ((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) a196.hom.τ₃) (add_zero 1) =
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) Kwhole.hom).comp
        (alphaOld.comp (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) bOld) (add_zero 1)) (zero_add 1) := by
    erw [originalCurvePointSurfaceDegreeOneClass_nativeLarge217]
    rfl
  have hCoefficient :
      alphaOld.comp (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) bOld) (add_zero 1) =
      alpha.comp (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) bNew) (add_zero 1) :=
    (congrArg (fun z : Ext.{u + 1} (C := ModuleCat.{u} R)
        (Phi.obj W.X₃) (Phi.obj W.X₁) 1 =>
      z.comp (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) bOld) (add_zero 1)) hClass).trans
        (congrArg (fun q : Phi.obj W.X₁ ⟶ (pointCartierYonedaCoefficientComplex s).X₃ =>
          alpha.comp (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) q) (add_zero 1)) hTarget)
  exact hDegree.trans (congrArg (fun z : Ext.{u + 1} (C := ModuleCat.{u} R)
      (Phi.obj W.X₃) (pointCartierYonedaCoefficientComplex s).X₃ 1 =>
    (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) Kwhole.hom).comp z (zero_add 1)) hCoefficient)

theorem originalSurfaceFirstCartier_wholeClass_cut217
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [hExtOriginalCurve : HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    [hExtOriginalSurface : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))))] :
    let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) :=
      hExtOriginalSurface
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
    let F := schemeModuleStalkModuleFunctor X x
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) := S.map F
    let s := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
    let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
    let Q := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {s}))
    let eta := ModuleCat.restrictScalarsComp' (Ideal.Quotient.mk (Ideal.span {s}))
      eQ.toRingHom (f.stalkMap x).hom
        (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
    let beta :
        (closedImmersionIdealTwistSequence (i ≫ f)
          (show (hypersurface p hp).Modules from
            SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃ ≅
        (Scheme.Modules.pushforward f).obj S.X₃ :=
      originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
    let etaM : H.obj ((Scheme.Modules.pushforward f).obj S.X₃) ≅ Phi.obj W.X₃ :=
      pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
    let Kwhole := Iso.trans
      (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
      (H.mapIso beta) etaM
    let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let hs := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom x) j hx
    ∀ (t : X.presheaf.stalk x) (ht : t ∈ (X.presheaf.stalk x)⁰)
      (a : W ≅ pointCartierYonedaCoefficientComplex t)
      (ha₁ : a.hom.τ₁ = (schemeModuleUnitStalkIso X x).hom),
    let aC := quotientWholePrincipalIso202 s eQ W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} _) ⥤ _).mapIso aC
    ((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) a196.hom.τ₁) (add_zero 2) =
      ((Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) Kwhole.hom).comp
        ((ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
            ((hS.map_of_exact F).map_of_exact Phi)).comp
          (Ext.mk₀.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) ((eta.app W.X₁).hom ≫ Q.map e₁.hom)) (add_zero 1)) (zero_add 1)).comp
        (ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
          (pointCartierYonedaCoefficientComplex_shortExact s hs)) rfl := by
  dsimp only
  let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) :=
    hExtOriginalSurface
  let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
  let F := schemeModuleStalkModuleFunctor X x
  let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
  let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk x)) := S.map F
  let s := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
  let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
  let Q := ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (Ideal.span {s}))
  let eta := ModuleCat.restrictScalarsComp'.{u} (Ideal.Quotient.mk (Ideal.span {s}))
    eQ.toRingHom (f.stalkMap x).hom
      (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
  let beta :
      (closedImmersionIdealTwistSequence (i ≫ f)
        (show (hypersurface p hp).Modules from
          SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward f).obj S.X₃ :=
    originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
  let etaM : H.obj ((Scheme.Modules.pushforward f).obj S.X₃) ≅ Phi.obj W.X₃ :=
    pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
  let Kwhole := Iso.trans
    (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
    (H.mapIso beta) etaM
  let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
  let hs := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom x) j hx
  let R := (hypersurface p hp).presheaf.stalk (f x)
  intro t ht a ha₁
  let aC := quotientWholePrincipalIso202 s eQ W t ht a
  let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} _) ⥤ _).mapIso aC
  let delta : Ext.{u + 1} (C := ModuleCat.{u} R)
      (pointCartierYonedaCoefficientComplex s).X₃ (pointCartierYonedaCoefficientComplex s).X₁ 1 :=
    ShortComplex.ShortExact.extClass.{u + 1} (C := ModuleCat.{u} R)
      (pointCartierYonedaCoefficientComplex_shortExact s hs)
  have hFirst :
      ((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) a196.hom.τ₁) (add_zero 2) =
      (((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) a196.hom.τ₃) (add_zero 1)).comp delta rfl := by
    erw [originalCurvePointSurfaceFirstCartierClass_native210]
    rfl
  have hDegree := originalSurfaceDegreeOne_wholeCoefficient_cut217 p l hp hp0 hl hl0
    X e i hS E x j hx t ht a ha₁
  exact hFirst.trans (congrArg (fun z : Ext.{u + 1} (C := ModuleCat.{u} R)
      (H.obj (closedImmersionIdealTwistSequence (i ≫ f)
        (show (hypersurface p hp).Modules from
          SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃)
      (pointCartierYonedaCoefficientComplex s).X₃ 1 =>
    z.comp delta rfl) hDegree)

end PfaffianDescent.Coray
