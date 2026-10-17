import PfaffianDescent.ActualSupportedPointScalarUnitSquare221
import PfaffianDescent.OriginalCurvePointSurfaceFirstCartier210

/-! SOURCE ONLY221. Actual field-scalar sections of the SAME whole point
quotient feed the original connecting map, then the actual plane boundary.
This proves a unit-family identity, not nonvanishing of a unit pullback. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe w w' v v' u u'

/-- Pure Yoneda reassociation; its square is proved geometrically by the
public221 actual-map theorem before this lemma is used at the caller. -/
private theorem supportedPointCartier_unitReassociation221
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasExt.{w} C] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {U Q N : C} {V T A B : D}
    (gamma : V ⟶ T) (sigma : T ⟶ T) (b : T ⟶ F.obj Q)
    (eta : V ⟶ F.obj U) (a : U ⟶ Q)
    (hsquare : gamma ≫ sigma ≫ b = eta ≫ F.map a)
    (z : Ext.{w} Q N 1) (v : F.obj N ⟶ A) (d : Ext.{w'} A B 1) :
    (Ext.mk₀ gamma).comp
      ((Ext.mk₀ sigma).comp
        (((Ext.mk₀ b).comp ((z.mapExactFunctor F).comp (Ext.mk₀ v) (add_zero 1))
          (zero_add 1)).comp d rfl) (zero_add 2)) (zero_add 2) =
    (((Ext.mk₀ eta).comp
        (((Ext.mk₀ a).comp z (zero_add 1)).mapExactFunctor F) (zero_add 1)).comp
      (Ext.mk₀ v) (add_zero 1)).comp d rfl := by
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc, Ext.mk₀_comp_mk₀_assoc, Category.assoc]
  rw [hsquare]

end PfaffianDescent
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open SchemeModuleInternalHom IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-- SAME original maps and whole Ext classes, with an inferred Yoneda-law output.
All object and exact-functor dictionaries are fixed to their native consumers. -/
private def originalCurvePointScalarRawUnitReassociation221
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (a : L) := by
  let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let G : X.Modules ⥤ (hypersurface p hp).Modules := Scheme.Modules.pushforward s
  letI hLimits : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (SheafOfModules.pushforward s.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI hAdd : G.Additive := Functor.additive_of_preserves_binary_products G
  let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)
  let beta := originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
  let gamma := closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ c.inv
  let sigma := c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ c.inv
  let aQ := closedImmersionUnitToPushforwardUnit i ≫
    fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv
  have hSquare : gamma ≫ sigma ≫ beta.hom =
      closedImmersionUnitToPushforwardUnit s ≫ G.map aQ :=
    actualSupportedPointWholeSource_scalarUnitSquare221 s i _ E a
  let hCategoryC : Category.{u} X.Modules := inferInstance
  let hAbelianC : Abelian X.Modules := inferInstance
  let hCategoryD : Category.{u} (hypersurface p hp).Modules := inferInstance
  let hAbelianD : Abelian (hypersurface p hp).Modules := inferInstance
  let hExtC : HasExt.{u} X.Modules := inferInstance
  let hExtD : HasExt.{u} (hypersurface p hp).Modules := inferInstance
  letI hColimits : PreservesFiniteColimits G :=
    schemeModulePushforward_preservesFiniteColimits_of_closedImmersion s
  let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let R : ShortComplex (hypersurface p hp).Modules :=
    homogeneousRestrictionSequence (grading (equationIdeal p hp))
      (cubicSecondEquationHomogeneous p l hp 1 hl) 0
  let P : ShortComplex (hypersurface p hp).Modules :=
    closedImmersionIdealTwistSequence (i ≫ s)
      (show (hypersurface p hp).Modules from SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
  exact @supportedPointCartier_unitReassociation221.{u, u, u, u, u + 1, u + 1}
    X.Modules hCategoryC hAbelianC
    (hypersurface p hp).Modules hCategoryD hAbelianD hExtC hExtD
    G hAdd hLimits hColimits
    (SheafOfModules.unit X.ringCatSheaf) S.X₃ S.X₁
    (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) P.X₃ R.X₃ R.X₁
    gamma sigma beta.hom (closedImmersionUnitToPushforwardUnit s) aQ hSquare
    (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hS)
    (originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e).hom
    (ShortComplex.ShortExact.extClass.{u} (C := (hypersurface p hp).Modules)
      (cubicSecondEquation_homogeneousRestrictionSequence_shortExact p l hp hp0 1 hl
        (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0) 0))

/-- Unit pullback of the actual210 class after an actual surface-point
scalar equals pushforward of the SAME original section boundary, followed
by the SAME plane Cartier boundary. The square is constructed, not assumed. -/
theorem originalCurvePointSurfaceFirstCartier_unitScalar221
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (a : L) :
    let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let G := Scheme.Modules.pushforward s
    let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)
    let gamma := closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ c.inv
    let sigma := c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ c.inv
    let aQ := closedImmersionUnitToPushforwardUnit i ≫
      fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv
    let delta := (Ext.mk₀.{u} (C := X.Modules) aQ).comp
      (ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hS) (zero_add 1)
    let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
    let d := ShortComplex.ShortExact.extClass.{u} (C := (hypersurface p hp).Modules)
      (cubicSecondEquation_homogeneousRestrictionSequence_shortExact p l hp hp0 1 hl
        (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0) 0)
    (Ext.mk₀.{u} (C := (hypersurface p hp).Modules) gamma).comp
      ((Ext.mk₀.{u} (C := (hypersurface p hp).Modules) sigma).comp
        (originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E)
        (zero_add 2)) (zero_add 2) =
    (((Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
        (closedImmersionUnitToPushforwardUnit s)).comp
        (Ext.mapExactFunctor.{u, u} (C := X.Modules) (D := (hypersurface p hp).Modules)
          G delta) (zero_add 1)).comp
      (Ext.mk₀.{u} (C := (hypersurface p hp).Modules) v.hom) (add_zero 1)).comp d rfl := by
  dsimp only
  have hRaw := originalCurvePointScalarRawUnitReassociation221 p l hp hp0 hl hl0 X e i hS E a
  dsimp only [originalCurvePointSurfaceFirstCartierClass210,
    originalCurvePointSurfaceDegreeOneClass210]
  exact hRaw

/-- If every scalar section is killed by the original connecting map, then
every actual supported surface scalar has zero unit restriction. The whole
point quotient and its actual projection are retained. No converse is inferred
from mere nonzero supported Ext. -/
theorem originalCurvePointSurfaceFirstCartier_unitScalar_eq_zero_of_boundaryFamily221
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (hzero : ∀ a : L,
      (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫
          fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
        hS.extClass (zero_add 1) = 0) :
    let s := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)
    ∀ a : L,
      (Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
        (closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ c.inv)).comp
        ((Ext.mk₀.{u} (C := (hypersurface p hp).Modules)
          (c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ c.inv)).comp
          (originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E)
          (zero_add 2)) (zero_add 2) = 0 := by
  dsimp only
  intro a
  rw [originalCurvePointSurfaceFirstCartier_unitScalar221 p l hp hp0 hl hl0 X e i hS E a,
    hzero a, Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp, Ext.zero_comp]

end PfaffianDescent.Coray
