import PfaffianDescent.OriginalCurvePointSurfaceFirstCartier210
import PfaffianDescent.ActualClosedPointGlobalDualQuotientSupport203
import PfaffianDescent.OriginalPlaneCubicClosedPointDVR200

/-! Genuine original point geometry constructs the supported surface class
and its native first-Cartier formula. No class or nonvanishing certificate. -/
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

/-- The coefficient extension of the SAME original nonzero cubic is
nonzero; this geometric input is derived, not requested from the caller. -/
lemma originalCubicCoefficientExtension_ne_zero210
    (p : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) :
    p.map (algebraMap K (GenericHyperplaneField K)) ≠ 0 := by
  intro hz
  apply hp0
  apply MvPolynomial.map_injective (algebraMap K (GenericHyperplaneField K))
    (algebraMap K (GenericHyperplaneField K)).injective
  simpa only [map_zero] using hz

/-- Exact data statement for the genuine original supported class. This
abbreviation names the complete endpoint identity; it is printed in drivers. -/
def originalCurvePointSurfaceNativeData210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    (P : closedPoints X) (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom P.1))))] : Prop :=
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
    let D := dual (closedImmersionModule i)
    let H := schemeModuleStalkModuleFunctor (hypersurface p hp)
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom P.1))
    let a := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (e.hom P.1) j hx
    let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (e.hom P.1) j hx
    ∃ hS : S.ShortExact,
    ∃ b : (Scheme.Modules.pullback i).obj D ≅
      (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
    ∃ E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
      S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
        (Scheme.Modules.pushforward i).map b.hom ∧
      ((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀ a.hom.τ₁) (add_zero 2) =
      (((originalCurvePointSurfaceDegreeOneClass210 p l hp hp0 hl hl0 X e i hS E).mapExactFunctor H).comp
        (Ext.mk₀ a.hom.τ₃) (add_zero 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact _ hf).extClass rfl

/-- The SAME original curve/point constructs every whole support coordinate
and the actual supported class internally. Ordinary original geometric
hypotheses suffice; no extension/support/comparison/nonzero premise is used. -/
theorem originalCurvePoint_exists_surfaceFirstCartierNative210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [IsIntegral X] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j)
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk
      (cubicSecondEquationCurveImmersion p l hp 1 hl (e.hom P.1))))] :
    originalCurvePointSurfaceNativeData210 p l hp hp0 hl hl0 X e P j hx := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨hS, b, E, hprojection⟩ := actualClosedPoint_exists_globalDualQuotientSupport203 X P
  refine ⟨hS, b, E, hprojection, ?_⟩
  exact originalCurvePointSurfaceFirstCartierClass_native210 p l hp hp0 hl hl0 X e i hS E P.1 j hx

/-- The literal genericPlaneCubic of the ORIGINAL smooth cubic constructs
the supported surface class. Integral/Noetherian/DVR and source-Scheme-Iso
inputs are derived from200/196 geometry, never supplied as certificates. -/
theorem originalGenericPlanePoint_exists_surfaceFirstCartierNative210
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion (p.map (algebraMap K (GenericHyperplaneField K)))
      (genericHyperplaneEquation (K := K)) (hp.map _) 1
      genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1) ∈
        quotientCoordinateOpen (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K)))
          (hp.map _)) j) :
    let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let pL := p.map (algebraMap K (GenericHyperplaneField K))
    let hpL := hp.map (algebraMap K (GenericHyperplaneField K))
    let hpL0 := originalCubicCoefficientExtension_ne_zero210 p hp0
    letI : Smooth (hypersurfaceToBase pL hpL) :=
      smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
    ∀ (hExtX : HasExt.{u} X.Modules)
      (hExtSurface : HasExt.{u} (hypersurface pL hpL).Modules)
      (hExtLocalSurface : HasExt.{u + 1} (ModuleCat ((hypersurface pL hpL).presheaf.stalk
        (cubicSecondEquationCurveImmersion pL (genericHyperplaneEquation (K := K)) hpL 1
          genericHyperplaneEquation_isHomogeneous ((genericPlaneCubicPairSchemeIso p hp).hom P.1))))),
    letI := hExtX
    letI := hExtSurface
    letI := hExtLocalSurface
    originalCurvePointSurfaceNativeData210 pL (genericHyperplaneEquation (K := K)) hpL hpL0
      genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
      X (genericPlaneCubicPairSchemeIso p hp) P j hx := by
  dsimp only
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) :=
    smooth_hypersurfaceToBase_map (algebraMap K (GenericHyperplaneField K)) p hp
  intro hExtX hExtSurface hExtLocalSurface
  letI := hExtX
  letI := hExtSurface
  letI := hExtLocalSurface
  let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : Smooth (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)) :=
    smoothCubic_actualGenericPlaneCubic_smooth p hp hp0
  letI : IsIntegral X := smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (hypersurfaceToBase (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
  letI : IsDiscreteValuationRing (X.presheaf.stalk P.1) :=
    smoothCubic_actualGenericPlaneCubic_closedPoint_stalk_isDVR200 p hp hp0 P
  exact originalCurvePoint_exists_surfaceFirstCartierNative210 _ _ _
    (originalCubicCoefficientExtension_ne_zero210 p hp0)
    genericHyperplaneEquation_isHomogeneous genericHyperplaneEquation_ne_zero
    X (genericPlaneCubicPairSchemeIso p hp) P j hx

end PfaffianDescent.Coray
