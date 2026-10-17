import PfaffianDescent.OriginalCurveSurfaceSupportedCoordinates210
import PfaffianDescent.NativePointExtensionEndpoints210

/-! Actual supported surface Ext2 class from the original curve point
extension; its native first-Cartier formula is derived from196. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open SchemeModuleInternalHom IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual supported degree-one class is constructed by the original
point extension, the actual source coordinate, and the actual curve-unit
cokernel coordinate. No comparison or nonzero class is an input. -/
def originalCurvePointSurfaceDegreeOneClass210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    Ext.{u} (C := (hypersurface p hp).Modules)
      (closedImmersionIdealTwistSequence
        (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl))
          (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (homogeneousRestrictionSequence (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) 0).X₃ 1 :=
  (Ext.mk₀ (originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E).hom).comp
    ((hS.extClass.mapExactFunctor (Scheme.Modules.pushforward
      (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl))).comp
        (Ext.mk₀ (originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e).hom)
        (add_zero 1)) (zero_add 1)

/-- SAME original point extension followed by the actual plane-Cartier
extension. Its source is the literal canonical surface point sequence target
required by the already-proven smooth-point boundary/trace criterion. -/
def originalCurvePointSurfaceFirstCartierClass210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hS : (incrementCokernelSequence (closedImmersionModuleToUnit i)).ShortExact)
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    Ext.{u} (C := (hypersurface p hp).Modules)
      (closedImmersionIdealTwistSequence
        (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl))
          (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 :=
  (originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).comp
    (ShortComplex.ShortExact.extClass.{u} (C := (hypersurface p hp).Modules)
      (cubicSecondEquation_homogeneousRestrictionSequence_shortExact p l hp hp0 1 hl
        (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0) 0)) rfl

/-- Native local first-Cartier formula for this ACTUAL constructed point
class. The original curve/unit/source coordinates are retained. This is an
identity, not an assumed coefficient match or local-to-global inference. -/
theorem originalCurvePointSurfaceFirstCartierClass_native210
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
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))))] :
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))
    let a := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom x) j hx
    ((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
      (Ext.mk₀ a.hom.τ₁) (add_zero 2) =
      (((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀ a.hom.τ₃) (add_zero 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact _ hf).extClass rfl :=
  originalPlaneZeroRestrictionStalk_boundary196 p l hp hp0 hl hl0 (e.hom x) j hx
    ((closedImmersionIdealTwistSequence
      (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl))
        (show (hypersurface p hp).Modules from
          SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃)
    (originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E)


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The supported native degree-one class is the SAME original whole point
stalk extension restricted along the literal original curve stalkMap. Its
actual source and unit/quotient coordinates are named in full; the comparison
follows from the EXISTING pushforward-stalk Ext theorem, not a premise. -/
theorem originalCurvePointSurfaceDegreeOneClass_native210
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
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x))))] :
    let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
    let F := schemeModuleStalkModuleFunctor X x
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
    let a := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let beta := originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
    let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
    let etaM := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
    let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₁
    ((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
      (Ext.mk₀ a.hom.τ₃) (add_zero 1) =
      (Ext.mk₀ (H.map beta.hom ≫ etaM.hom)).comp
        (((hS.map_of_exact F).extClass.mapExactFunctor Phi).comp
          (Ext.mk₀ (etaN.inv ≫ H.map v.hom ≫ a.hom.τ₃)) (add_zero 1)) (zero_add 1) := by
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  dsimp only
  let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let hExtSurface : HasExt.{u} (hypersurface p hp).Modules := inferInstance
  let hExtCurveStalk : HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x)) :=
    inferInstance
  let hExtNativeSurface : HasExt.{u}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) := inferInstance
  let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
  let beta := originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X e i E
  let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
  change (((Ext.mk₀ beta.hom).comp
      ((hS.extClass.mapExactFunctor (Scheme.Modules.pushforward f)).comp
        (Ext.mk₀ v.hom) (add_zero 1)) (zero_add 1)).mapExactFunctor H).comp
    (Ext.mk₀ (originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0
      (e.hom x) j hx).hom.τ₃) (add_zero 1) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  let F := schemeModuleStalkModuleFunctor X x
  let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
  let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let a := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
  let etaM := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₃
  let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x S.X₁
  let alpha : Ext.{u} (C := X.Modules) S.X₃ S.X₁ 1 :=
    ShortComplex.ShortExact.extClass.{u} (C := X.Modules) hS
  let alphaY : Ext.{u} (C := (hypersurface p hp).Modules)
      ((Scheme.Modules.pushforward f).obj S.X₃) ((Scheme.Modules.pushforward f).obj S.X₁) 1 :=
    alpha.mapExactFunctor (Scheme.Modules.pushforward f)
  let A : Ext.{u} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
      (H.obj ((Scheme.Modules.pushforward f).obj S.X₃))
      (H.obj ((Scheme.Modules.pushforward f).obj S.X₁)) 1 :=
    @Ext.mapExactFunctor.{u, u} (hypersurface p hp).Modules _ _
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) _ _
      H _ _ _ hExtSurface hExtNativeSurface _ _ _ alphaY
  let B : Ext.{u + 1} (C := ModuleCat.{u} (X.presheaf.stalk x))
      (F.obj S.X₃) (F.obj S.X₁) 1 := alpha.mapExactFunctor F
  let C : Ext.{u} (C := ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x)))
      (Phi.obj (F.obj S.X₃)) (Phi.obj (F.obj S.X₁)) 1 :=
    @Ext.mapExactFunctor.{u + 1, u}
      (ModuleCat.{u} (X.presheaf.stalk x)) _ _
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) _ _
      Phi _ _ _ hExtCurveStalk hExtNativeSurface _ _ _ B
  have hNatural : A.comp (Ext.mk₀.{u} etaN.hom) (add_zero 1) =
      (Ext.mk₀.{u} etaM.hom).comp C (zero_add 1) := by
    dsimp only [A, C, B, alphaY]
    rw [pointCartierNativeStalkExtFunctorComposition,
      pointCartierNativeStalkExtFunctorComposition]
    exact pointCartierNativeStalkExtFunctorNaturality _ _
      (pointCartierNativeStalkPushforwardNatIso f f.isClosedEmbedding.isInducing x).hom alpha
  have hPost : A.comp (Ext.mk₀.{u} (H.map v.hom ≫ a.hom.τ₃)) (add_zero 1) =
      (Ext.mk₀.{u} etaM.hom).comp
        (C.comp (Ext.mk₀.{u} (etaN.inv ≫ H.map v.hom ≫ a.hom.τ₃))
          (add_zero 1)) (zero_add 1) := by
    calc
      _ = (A.comp (Ext.mk₀.{u} etaN.hom) (add_zero 1)).comp
          (Ext.mk₀.{u} (etaN.inv ≫ H.map v.hom ≫ a.hom.τ₃)) (add_zero 1) := by
        rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [hNatural, Ext.comp_assoc_of_third_deg_zero]
  have hEndpoint :
      (Ext.mk₀.{u} (H.map beta.hom)).comp
        (A.comp (Ext.mk₀.{u} (H.map v.hom ≫ a.hom.τ₃)) (add_zero 1)) (zero_add 1) =
      (Ext.mk₀.{u} (H.map beta.hom ≫ etaM.hom)).comp
        (C.comp (Ext.mk₀.{u} (etaN.inv ≫ H.map v.hom ≫ a.hom.τ₃))
          (add_zero 1)) (zero_add 1) := by
    rw [hPost, Ext.mk₀_comp_mk₀_assoc]
  have hClass : B = ShortComplex.ShortExact.extClass.{u + 1}
      (C := ModuleCat.{u} (X.presheaf.stalk x)) (hS.map_of_exact F) :=
    Ext.mapExactFunctor_extClass F hS
  exact hEndpoint.trans (congrArg (fun w : Ext.{u + 1}
      (C := ModuleCat.{u} (X.presheaf.stalk x)) (F.obj S.X₃) (F.obj S.X₁) 1 =>
    (Ext.mk₀.{u} (H.map beta.hom ≫ etaM.hom)).comp
      ((@Ext.mapExactFunctor.{u + 1, u}
          (ModuleCat.{u} (X.presheaf.stalk x)) _ _
          (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (f x))) _ _
          Phi _ _ _ hExtCurveStalk hExtNativeSurface _ _ _ w).comp
        (Ext.mk₀.{u} (etaN.inv ≫ H.map v.hom ≫ a.hom.τ₃)) (add_zero 1))
      (zero_add 1)) hClass)

end PfaffianDescent.Coray
