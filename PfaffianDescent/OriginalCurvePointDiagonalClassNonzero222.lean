import PfaffianDescent.ActualFlatPullbackCoefficientNonzero222
import PfaffianDescent.OriginalSupportedSurfaceClassNonzero220
import AllCharacteristics.ClosedPointAlgebra

/-! SAME original curve/point extension and SAME218 witnesses give a
nonzero actual finite-separable diagonal class. CharZero is used only to
derive residue separability, never inferred from smoothness alone. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective PfaffianDescent.ProjectiveNegativeTwist PfaffianDescent.IdealSheafDataModule
open PfaffianDescent.SchemeModuleInternalHom
open scoped nonZeroDivisors
namespace PfaffianDescent.Coray
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- Actual geometric diagonal nonvanishing with no coefficient comparison,
proper ideal or nonzero certificate as an input. The point-to-base action is
the native pointAlgebra of the ORIGINAL curve map to the ORIGINAL field. -/
theorem originalCurvePoint_exists_nonzeroDiagonalSupportedClass222
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (eX : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    [IsIntegral X] [IsLocallyNoetherian X]
    [HasExt.{u} X.Modules] [HasExt.{u} (hypersurface p hp).Modules]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk P.1))]
    (j : Fin 4)
    (hx : cubicSecondEquationCurveImmersion p l hp 1 hl (eX.hom P.1) ∈
      quotientCoordinateOpen (equationIdeal p hp) j) :
    let Y := hypersurface p hp
    let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
    let pi := hypersurfaceToBase p hp
    let piX := s ≫ pi
    letI := AllCharacteristics.pointAlgebra piX P.1
    let L := X.residueField P.1
    letI : Module.Finite K L := AllCharacteristics.closedPoint_moduleFinite piX P
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let iY := i ≫ s
    let hi : iY ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      exact (Category.assoc i s pi).trans (AllCharacteristics.pointAlgebra_spec piX P.1).symm
    let YL := schemeBaseChangeToField (L := L) Y pi
    let q := cubicPointTraceFieldBaseChangeProjection K L pi
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let jY := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L pi iY hi
    let xL := jY (d (default : Spec (.of L)))
    let R := Y.presheaf.stalk (s P.1)
    let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    ∀ (hExtR : HasExt.{u + 1} (ModuleCat.{u} R))
      (hExtC : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {f})))
      (hExtYL : HasExt.{u} YL.Modules)
      (hExtRL : HasExt.{u + 1} (ModuleCat.{u} (YL.presheaf.stalk xL))),
    letI := hExtR
    letI := hExtC
    letI := hExtYL
    letI := hExtRL
    ∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)),
      let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E
      let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
      let zPoint := (Ext.mk₀.{u} (C := Y.Modules) c.inv).comp z (zero_add 2)
      let zDiagonal := cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi iY hi _ 2 zPoint
      zDiagonal.mapExactFunctor (schemeModuleStalkModuleFunctor YL xL) ≠ 0 ∧
      zDiagonal ≠ 0 := by
  classical
  dsimp only
  intro hExtR hExtC hExtYL hExtRL
  letI := hExtR
  letI := hExtC
  letI := hExtYL
  letI := hExtRL
  let Y := hypersurface p hp
  letI : EnoughInjectives Y.Modules := sheafOfModules_enoughInjectives Y.ringCatSheaf
  let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let pi := hypersurfaceToBase p hp
  let piX := s ≫ pi
  letI := AllCharacteristics.pointAlgebra piX P.1
  let L := X.residueField P.1
  letI : Module.Finite K L := AllCharacteristics.closedPoint_moduleFinite piX P
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let iY := i ≫ s
  let hi : iY ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (Category.assoc i s pi).trans (AllCharacteristics.pointAlgebra_spec piX P.1).symm
  let YL := schemeBaseChangeToField (L := L) Y pi
  let q := cubicPointTraceFieldBaseChangeProjection K L pi
  let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
  let jY := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L pi iY hi
  let xL := jY (d (default : Spec (.of L)))
  let H := schemeModuleStalkModuleFunctor YL xL
  have hpoint : q xL = s P.1 := by
    calc
      q xL = q ((cubicPointTraceFieldBaseChangeRationalPoint K L pi iY hi)
          (default : Spec (.of L))) := by
        change q ((d ≫ jY) (default : Spec (.of L))) = _
        rw [cubicPointTraceFieldBaseChangeTensorDiagonal_comp_ambient]
      _ = iY (default : Spec (.of L)) :=
        congrArg (fun a => a (default : Spec (.of L)))
          (cubicPointTraceFieldBaseChangeRationalPoint_fst K L pi iY hi)
      _ = s P.1 := by simp only [iY, i, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  obtain ⟨hS, E, _, g, hg, kappa, hfm, hgm, hproper, hCoefficient, hLocal⟩ :=
    originalCurvePoint_exists_nonzeroSupportedSurfaceClass220 p l hp hp0 hl hl0 X eX P j hx
      hExtR hExtC
  let z := originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E
  let beta := originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X eX i E
  let etaM := pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing P.1
    (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃
  let Kwhole := (schemeModuleStalkModuleFunctor Y (s P.1)).mapIso beta ≪≫ etaM
  let lambdaOne := supportedWholeCoefficientOneAugmentation217 Kwhole kappa
  let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
  have hPullback : (cubicPointTraceFieldBaseChangeFlatPullbackExtMap q _ _ 2 z).mapExactFunctor H ≠ 0 :=
    actualFlatPullbackStalk_nonzero_of_localSerreCoefficient_atPoint222 q xL (s P.1) hpoint z
      _ g _ hg hfm hgm lambdaOne a196.hom.τ₁ hCoefficient
  let c := closedImmersionIdealTwistSequenceUnitTargetIso iY
  let zPoint := (Ext.mk₀.{u} (C := Y.Modules) c.inv).comp z (zero_add 2)
  have hPointPullback :
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap q _ _ 2 zPoint).mapExactFunctor H ≠ 0 := by
    intro hz
    change ((zPoint.mapExactFunctor (Scheme.Modules.pullback q)).mapExactFunctor H) = 0 at hz
    dsimp only [zPoint] at hz
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at hz
    exact hPullback ((ext_precomp_isIso_eq_zero_iff222 _ 2 _).mp hz)
  let zDiagonal := cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi iY hi _ 2 zPoint
  have hDiagonal : zDiagonal.mapExactFunctor H ≠ 0 := by
    intro hz
    exact hPointPullback ((cubicPointTraceFieldBaseChangeDiagonalExtClass_stalk_zero_iff222
      K L pi iY hi _ 2 zPoint hExtRL).mp hz)
  refine ⟨hS, E, hDiagonal, ?_⟩
  intro hz
  have hzNative : zDiagonal = 0 := hz
  apply hDiagonal
  rw [hzNative, Ext.mapExactFunctor_zero]

end PfaffianDescent.Coray
