import PfaffianDescent.SchemeModuleInternalHomSupportedFiberIso
import PfaffianDescent.CorayNormalizationClosedPointCanonicalFiber

/-! Primitive actual normalization-point callers for the canonical
intrinsic fiber Iso. Original p/q geometry internally supplies every
ideal chart and the factor through the chart containing P. The target
is the SAME i_*i^*D, with the SAME adjunction unit and original global
cokernel projection. No invertibility, quotient or RR certificate is
input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Transport the complete actual projection proposition along a native
morphism equality before any original normalization is specialized. -/
private theorem nativeDualTensorProjectionTransport001
    {X Z : Scheme.{u}} {f g : Z ⟶ X} (h : f = g)
    (hf : IsIso (schemeModuleCanonicalFiberProjection f
      (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule f)))) :
    IsIso (schemeModuleCanonicalFiberProjection g
      (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule g))) := by
  cases h
  exact hf

/-- Transport the ENTIRE existential Iso/projection/uniqueness predicate.
Every object and map changes together along the SAME original equality. -/
private theorem nativeDualCanonicalFiberIsoTransport001
    {X Z : Scheme.{u}} {f g : Z ⟶ X} (h : f = g)
    (hf :
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule f)
      let delta := SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit f)
      ∃ E : cokernel delta ≅ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj D),
        cokernel.π delta ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app D ∧
        ∀ F : cokernel delta ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj D),
          cokernel.π delta ≫ F = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app D →
          F = E.hom) :
    let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule g)
    let delta := SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit g)
    ∃ E : cokernel delta ≅ (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj D),
      cokernel.π delta ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app D ∧
      ∀ F : cokernel delta ⟶ (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj D),
        cokernel.π delta ≫ F = (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app D →
        F = E.hom := by
  cases h
  exact hf

/-- The SAME canonical projection formula for the original constructed
dual and the actual normalization residue point is invertible. Every
chart and support factor is internally derived from primitive geometry. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_tensorProjection_isIso
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      IsIso (schemeModuleCanonicalFiberProjection i
        (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))) := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let B : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hB (x : N) : x ∈ (B x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.obj (op (B x).1) :=
    Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (B x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  let eB (x : N) : M.over (B x).1 ≅ (SheafOfModules.unit N.ringCatSheaf).over (B x).1 := by
    letI := hm x
    let e : SheafOfModules.unit ((B x).1 : Scheme.{u}).ringCatSheaf ≅
        M.restrict (B x).1.ι := asIso (schemeModuleSectionOnOpenHom M (B x).1 (m x))
    exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (B x).1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso (B x).1).symm
  let U := (B P.1).1
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hB P.1⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let eB' (x : N) : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x).1 ≅
      (SheafOfModules.unit N.ringCatSheaf).over (B x).1 := by
    rw [hji]
    exact eB x
  have hlocal :=
    SchemeModuleInternalHom.closedImmersionDualIncrement_tensorProjection_isIso_of_factor_unitChart
      U j (fun x => (B x).1) hB eB' (eB' P.1)
  exact nativeDualTensorProjectionTransport001 (X := N) (f := j ≫ U.ι) (g := i)
    hji hlocal

/-- The GLOBAL increment cokernel is the actual intrinsic fiber
pushforward. The SAME original projection becomes the SAME actual
adjunction unit, and that equation uniquely determines the resulting
map. No chart-dependent bare residue-field target is declared canonical. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_canonicalFiberIso
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      let delta := SchemeModuleInternalHom.unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)
      ∃ E : cokernel delta ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D),
        cokernel.π delta ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ∧
        ∀ F : cokernel delta ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D),
          cokernel.π delta ≫ F = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D →
          F = E.hom := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let B : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hB (x : N) : x ∈ (B x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.obj (op (B x).1) :=
    Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (B x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  let eB (x : N) : M.over (B x).1 ≅ (SheafOfModules.unit N.ringCatSheaf).over (B x).1 := by
    letI := hm x
    let e : SheafOfModules.unit ((B x).1 : Scheme.{u}).ringCatSheaf ≅
        M.restrict (B x).1.ι := asIso (schemeModuleSectionOnOpenHom M (B x).1 (m x))
    exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (B x).1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso (B x).1).symm
  let U := (B P.1).1
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hB P.1⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let eB' (x : N) : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x).1 ≅
      (SheafOfModules.unit N.ringCatSheaf).over (B x).1 := by
    rw [hji]
    exact eB x
  let delta := SchemeModuleInternalHom.unitToHom
    (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι))
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι))
  have hresult : ∃ E : cokernel delta ≅
      (Scheme.Modules.pushforward (j ≫ U.ι)).obj ((Scheme.Modules.pullback (j ≫ U.ι)).obj D),
      cokernel.π delta ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ∧
      ∀ F : cokernel delta ⟶
        (Scheme.Modules.pushforward (j ≫ U.ι)).obj ((Scheme.Modules.pullback (j ≫ U.ι)).obj D),
        cokernel.π delta ≫ F = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D →
        F = E.hom := by
    let E := SchemeModuleInternalHom.closedImmersionDualIncrement_canonicalFiberIso
      U j (fun x => (B x).1) hB eB' (eB' P.1)
    have hE := SchemeModuleInternalHom.closedImmersionDualIncrement_canonicalFiberIso_projection
      U j (fun x => (B x).1) hB eB' (eB' P.1)
    refine ⟨E, hE, ?_⟩
    intro F hF
    exact (cancel_epi (cokernel.π delta)).mp (hF.trans hE.symm)
  exact nativeDualCanonicalFiberIsoTransport001 (X := N) (f := j ≫ U.ι) (g := i)
    hji hresult

end PfaffianDescent.Coray
