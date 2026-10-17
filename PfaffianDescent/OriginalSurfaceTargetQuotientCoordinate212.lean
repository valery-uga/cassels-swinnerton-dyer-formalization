import PfaffianDescent.NativeClosedUnitQuotientSquare212
import PfaffianDescent.OriginalSurfaceUnitProjection212
import PfaffianDescent.OriginalPlaneSourceIsoStalkQuotient196

/-! The literal TARGET in210 is the original quotient coordinate in202.
The quotient equivalence, unit square and epi cancellation are all derived.
This does not assert local-to-global nonvanishing. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The quotient identity is the literal original source stalkMap. -/
lemma originalSurfaceSource_stalkMap_quotient212
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    ((e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl).stalkMap x).hom =
      (originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.span {originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx})) := by
  apply RingHom.ext
  intro r
  exact (originalPlaneSourceIsoStalkQuotientEquiv_mk196 p l hp hp0 hl hl0 X e x j hx r).symm

/-- The actual supported-point TARGET coordinate in210, with the actual
native pushforward-stalk Iso, equals the constructed original quotient
coordinate. No target-coordinate equality or quotient square is a premise. -/
theorem originalSurfaceTarget_canonicalQuotientCoordinate212
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x
      (SheafOfModules.unit X.ringCatSheaf)
    let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
    let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let t := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
    let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
    etaN.inv ≫ H.map v.hom ≫ a196.hom.τ₃ =
      Phi.map (schemeModuleUnitStalkIso X x).hom ≫
        originalQuotientUnitCoordinate212 t eQ (f.stalkMap x).hom
          (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx) := by
  dsimp only
  let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
  let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
  let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x
    (SheafOfModules.unit X.ringCatSheaf)
  let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
  let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
  let t := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
  let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
  letI : IsClosedImmersion f := by
    dsimp only [f]
    infer_instance
  letI : Epi (closedImmersionUnitToPushforwardUnit f) := by
    change Epi (closedImmersionModulePushforwardSequence f).g
    exact (closedImmersionModulePushforwardSequence_shortExact f).epi_g
  let qNative := H.map (closedImmersionUnitToPushforwardUnit f)
  letI : Epi qNative := schemeModuleStalkModuleFunctor_map_epi
    (closedImmersionUnitToPushforwardUnit f) (f x)
  let b := Phi.map (schemeModuleUnitStalkIso X x).hom ≫
    originalQuotientUnitCoordinate212 t eQ (f.stalkMap x).hom
      (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
  let S := homogeneousRestrictionSequence (grading (equationIdeal p hp))
    (cubicSecondEquationHomogeneous p l hp 1 hl) 0
  let u := unitIsoZeroTwist (grading (equationIdeal p hp))
  let eUnit := schemeModuleUnitStalkIso (hypersurface p hp) (f x)
  have ha₂ : a196.hom.τ₂ = H.map u.inv ≫ eUnit.hom := rfl
  have hproj : H.map S.g ≫ a196.hom.τ₃ = a196.hom.τ₂ ≫
      (pointCartierYonedaCoefficientComplex t).g := a196.hom.comm₂₃.symm
  have hleft : qNative ≫ H.map v.hom ≫ a196.hom.τ₃ =
      eUnit.hom ≫ (pointCartierYonedaCoefficientComplex t).g := by
    change H.map (closedImmersionUnitToPushforwardUnit f) ≫ H.map v.hom ≫ a196.hom.τ₃ = _
    rw [← H.map_comp_assoc, originalCurveSurfaceUnitCokernelIso_unit212, H.map_comp,
      Category.assoc, hproj, ha₂]
    simp only [u, ← Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
      Category.id_comp]
  have hright : qNative ≫ etaN.hom ≫ b =
      eUnit.hom ≫ (pointCartierYonedaCoefficientComplex t).g :=
    nativeClosedUnit_originalQuotient_square212 f x t eQ
      (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
  exact originalUnitQuotientCoordinate_cancel212 qNative etaN (H.map v.hom)
    a196.hom.τ₃ b (hleft.trans hright.symm)

/-- For an entire original point complex, the SAME target is exactly the
202 quotient-coordinate expression. The supplied data are ordinary entire
complex/frame data; the original geometric factory below derives them. -/
theorem originalSurfaceTarget_wholeFirstCoordinate212
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    (x : X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom x) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    (W : ShortComplex (ModuleCat (X.presheaf.stalk x)))
    (t : X.presheaf.stalk x) (ht : t ∈ (X.presheaf.stalk x)⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t)
    (hunit : W.X₁ = (schemeModuleStalkModuleFunctor X x).obj
      (SheafOfModules.unit X.ringCatSheaf))
    (ha₁ : a.hom.τ₁ = eqToHom hunit ≫ (schemeModuleUnitStalkIso X x).hom) :
    let f := e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp) (f x)
    let s := originalPlaneSectionStalkScalar196 p l hp hl (e.hom x) j hx
    let eQ := originalPlaneSourceIsoStalkQuotientEquiv196 p l hp hp0 hl hl0 X e x j hx
    let q := Ideal.Quotient.mk (Ideal.span {s})
    let Q := ModuleCat.restrictScalars q
    let eta := ModuleCat.restrictScalarsComp' q eQ.toRingHom (f.stalkMap x).hom
      (originalSurfaceSource_stalkMap_quotient212 p l hp hp0 hl hl0 X e x j hx)
    let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x
      (SheafOfModules.unit X.ringCatSheaf)
    let v := originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e
    let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom x) j hx
    let aC := quotientWholePrincipalIso202 s eQ W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat _) ⥤ _).mapIso aC
    (ModuleCat.restrictScalars (f.stalkMap x).hom).map (eqToHom hunit) ≫
        etaN.inv ≫ H.map v.hom ≫ a196.hom.τ₃ =
      (eta.app W.X₁).hom ≫ Q.map e₁.hom := by
  dsimp only
  rw [originalSurfaceTarget_canonicalQuotientCoordinate212,
    quotientWholePrincipal_firstCoordinate212, ha₁, Functor.map_comp, Category.assoc]

end PfaffianDescent.Coray
