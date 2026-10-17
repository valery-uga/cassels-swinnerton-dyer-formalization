import PfaffianDescent.SchemeModuleInternalHomIncrementChartCokernel
import PfaffianDescent.CorayNormalizationClosedPointIdealDualEvaluation

/-! Primitive original p/q normalization caller for the SAME point ideal,
its ACTUAL O-linear dual, canonical increment map, genuine global short
exact cokernel sequence and original projection. Every unit chart and
regular coefficient is derived internally. Bare point-pushforward
identifications are only ACTUAL CHOSEN-CHART identifications, not an
assertion of a canonical generator-independent residue-field Iso.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Genuine primitive GLOBAL point increment with the SAME original
ideal inclusion, actual constructed dual and literal categorical
cokernel projection. Monicity and exactness are proved internally from
ordinary original p/q geometry. No increment or invertibility premise. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
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
      (SchemeModuleInternalHom.incrementCokernelSequence
        (IdealSheafDataModule.closedImmersionModuleToUnit i)).ShortExact := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let B : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hB (x : N) : x ∈ (B x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.obj (op (B x).1) :=
    Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (B x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  apply SchemeModuleInternalHom.incrementCokernelSequence_shortExact_of_pointwise_unitCharts
    (IdealSheafDataModule.closedImmersionModuleToUnit i) (fun x => (B x).1) hB
  intro x
  letI := hm x
  let e : SheafOfModules.unit ((B x).1 : Scheme.{u}).ringCatSheaf ≅
      M.restrict (B x).1.ι := asIso (schemeModuleSectionOnOpenHom M (B x).1 (m x))
  exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (B x).1 e.symm ≪≫
    (SchemeModuleInternalHom.unitOverIso (B x).1).symm

/-- At EVERY point, on an actual affine chart, the GLOBAL increment
cokernel has a CHOSEN-FRAME Iso to the SAME original point unit
pushforward. Its square retains the SAME canonical cokernel projection
and SAME original residue restriction; the coefficient is internally
proved regular. No cokernel, residue or local comparison certificate is
supplied to this primitive endpoint. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_cokernel_charts
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ (P : closedPoints N) (x : N),
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      let j := IdealSheafDataModule.closedImmersionModuleToUnit i
      ∃ U : N.affineOpens, x ∈ U.1 ∧
        ∃ e : M.over U.1 ≅ (SheafOfModules.unit N.ringCatSheaf).over U.1,
          @IsRegular (Γ(N, U.1)) inferInstance (j.val.app (op U.1)
            ((SchemeModuleInternalHom.overTopLinearEquiv M U.1 e).symm 1)) ∧
          ∃ E : (cokernel (SchemeModuleInternalHom.unitToHom j)).over U.1 ≅
              ((Scheme.Modules.pushforward i).obj
                (SheafOfModules.unit (Spec (N.residueField P.1)).ringCatSheaf)).over U.1,
            (cokernel.π (SchemeModuleInternalHom.unitToHom j)).over U.1 ≫ E.hom =
              (SchemeModuleInternalHom.dualOverUnitIso U.1 e).hom ≫
                (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).over U.1 := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P x
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  letI : Mono j := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let B : N → N.affineOpens := fun y => Classical.choose (hc y)
  have hB (y : N) : y ∈ (B y).1 := (Classical.choose_spec (hc y)).1
  let m (y : N) : M.val.obj (op (B y).1) :=
    Classical.choose ((Classical.choose_spec (hc y)).2)
  have hm (y : N) : IsIso (schemeModuleSectionOnOpenHom M (B y).1 (m y)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc y)).2)).1
  let eB (y : N) : M.over (B y).1 ≅ (SheafOfModules.unit N.ringCatSheaf).over (B y).1 := by
    letI := hm y
    let e : SheafOfModules.unit ((B y).1 : Scheme.{u}).ringCatSheaf ≅
        M.restrict (B y).1.ι := asIso (schemeModuleSectionOnOpenHom M (B y).1 (m y))
    exact ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (B y).1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso (B y).1).symm
  refine ⟨B x, hB x, eB x, SchemeModuleInternalHom.inclusion_frame_isRegular j (B x).1 (eB x),
    SchemeModuleInternalHom.closedImmersionIncrement_cokernelOverIso
      i (fun y => (B y).1) hB eB (B x).1 (eB x), ?_⟩
  exact SchemeModuleInternalHom.closedImmersionIncrement_cokernelOverIso_projection
    i (fun y => (B y).1) hB eB (B x).1 (eB x)

end PfaffianDescent.Coray
