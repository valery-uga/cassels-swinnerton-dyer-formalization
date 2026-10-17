import PfaffianDescent.OriginalSurfaceParameterPairProper220
import PfaffianDescent.OriginalSurfaceFirstCartierPullback217
import PfaffianDescent.OriginalCurvePointSurfaceSourceFactory218
import PfaffianDescent.FlatKoszulClassNonzero211

/-! Original geometry constructs the SAME218 a/E/g/kappa.217 identifies
its coefficient-one pullback; actual localness derives source properness,
and the native unit-class theorem proves local and supported nonvanishing. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial IsLocalRing
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule SchemeModuleInternalHom
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL supported surface Ext2 class is nonzero. All whole point
and coefficient data are constructed internally from218. Neither a proper
parameter ideal nor a local/nonzero class is a premise. The existing218
local-nonzero output is deliberately not used: properness is derived from
actual original stalkMap images and211 proves local nonvanishing anew. -/
theorem originalCurvePoint_exists_nonzeroSupportedSurfaceClass220
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
    let R := Y.presheaf.stalk (s P.1)
    let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
    let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let F := schemeModuleStalkModuleFunctor X P.1
    let H := schemeModuleStalkModuleFunctor Y (s P.1)
    let Phi := ModuleCat.restrictScalars (s.stalkMap P.1).hom
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk P.1)) := S.map F
    ∀ (hExtR : HasExt.{u + 1} (ModuleCat.{u} R))
      (hExtC : HasExt.{u + 1} (ModuleCat.{u} (R ⧸ Ideal.span {f}))),
    letI := hExtR
    letI := hExtC
    ∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
      originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E ≠ 0 ∧
      ∃ (g : R) (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
        (kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃),
        f ∈ maximalIdeal R ∧ g ∈ maximalIdeal R ∧
        (1 : R) ∉ Ideal.span ({f, g} : Set R) ∧
        let beta : (closedImmersionIdealTwistSequence (i ≫ s)
            (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃ ≅
              (Scheme.Modules.pushforward s).obj S.X₃ :=
          originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X eX i E
        let etaM : H.obj ((Scheme.Modules.pushforward s).obj S.X₃) ≅ Phi.obj W.X₃ :=
          pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing P.1 S.X₃
        let Kwhole := Iso.trans (C := ModuleCat.{u} R) (H.mapIso beta) etaM
        let lambdaOne := supportedWholeCoefficientOneAugmentation217 Kwhole kappa
        let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
        (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) lambdaOne).comp
          (((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E).mapExactFunctor H).comp
            (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) a196.hom.τ₁) (add_zero 2)) (zero_add 2) =
          (@localSerreExtTwoClass.{u, u + 1} R inferInstance f g 1 hf hg hExtR) ∧
        (@localSerreExtTwoClass.{u, u + 1} R inferInstance f g 1 hf hg hExtR) ≠ 0 := by
  classical
  dsimp only
  intro hExtR hExtC
  letI := hExtR
  letI := hExtC
  let Y := hypersurface p hp
  let s := eX.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let F := schemeModuleStalkModuleFunctor X P.1
  let H := schemeModuleStalkModuleFunctor Y (s P.1)
  let R := Y.presheaf.stalk (s P.1)
  let Phi := ModuleCat.restrictScalars (s.stalkMap P.1).hom
  let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
  let W : ShortComplex (ModuleCat.{u} (X.presheaf.stalk P.1)) := S.map F
  let f := originalPlaneSectionStalkScalar196 p l hp hl (eX.hom P.1) j hx
  let hf := originalPlaneSectionStalkScalar_regular196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
  have hData := originalCurvePoint_exists_surfaceSourceUnitMatch218 p l hp hp0 hl hl0 X eX P j hx
  change originalCurvePointSurfaceSourceData218 p l hp hp0 hl hl0 X eX P j hx at hData
  dsimp only [originalCurvePointSurfaceSourceData218] at hData
  obtain ⟨hS, U, hPU, jP, hji, e, t, e0, hspan, ht, he0, a, ha1, ha2, b, E, hE, hRest⟩ := hData
  obtain ⟨g, hgt, hg, kappa, hProjection, hClass, _, hTheta, lambda, hFactor, hMatch, hEpi⟩ :=
    hRest hExtR hExtC
  obtain ⟨hfm, hgm, hproper⟩ :=
    originalSurfaceParameterPair_mem_maximal220 p l hp hp0 hl hl0 X eX P.1 j hx t hspan g hgt
  have hLocal : (@localSerreExtTwoClass.{u, u + 1} R inferInstance f g 1 hf hg hExtR) ≠ 0 :=
    @localSerreExtTwoClass_unit_ne_zero211.{u} R inferInstance hExtR f g 1 hf hg isUnit_one hproper
  have hNativePullback := originalSurfaceFirstCartier_wholePullback217
    (hExtOriginalSurface := hExtR) p l hp hp0 hl hl0
    X eX i hS E P.1 j hx t ht a ha1 _ kappa
  have hPullback := hNativePullback.trans hClass
  let beta : (closedImmersionIdealTwistSequence (i ≫ s)
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃ ≅
        (Scheme.Modules.pushforward s).obj S.X₃ :=
    originalCurvePointSurfaceSupportedSourceIso210 p l hp hl X eX i E
  let etaM : H.obj ((Scheme.Modules.pushforward s).obj S.X₃) ≅ Phi.obj W.X₃ :=
    pointCartierNativeStalkPushforwardIso s s.isClosedEmbedding.isInducing P.1 S.X₃
  let Kwhole := Iso.trans (C := ModuleCat.{u} R) (H.mapIso beta) etaM
  let lambdaOne := supportedWholeCoefficientOneAugmentation217 Kwhole kappa
  let a196 := originalPlaneZeroRestrictionStalkPrincipalIso196 p l hp hp0 hl hl0 (eX.hom P.1) j hx
  have hDetected : (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) lambdaOne).comp
      (((originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E).mapExactFunctor H).comp
        (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) a196.hom.τ₁) (add_zero 2)) (zero_add 2) ≠ 0 := by
    rw [hPullback]
    exact hLocal
  have hz : originalCurvePointSurfaceFirstCartierClass210 p l hp hp0 hl hl0 X eX i hS E ≠ 0 :=
    ext_ne_zero_of_nativeEndpointPullback220 (C := Y.Modules) (D := ModuleCat.{u} R)
      H _ lambdaOne a196.hom.τ₁ hDetected
  exact ⟨hS, E, hz, g, hg, kappa, hfm, hgm, hproper, hPullback, hLocal⟩

end PfaffianDescent.Coray
