import PfaffianDescent.SchemeModuleInternalHomRankOneInverse

/-! Primitive actual point-ideal caller for the CONSTRUCTED global dual
and canonical evaluation. Geometry internally supplies all rank-one
charts. Both the RAW evaluation components and GLOBAL sheafified
evaluation are proved invertible. A geometric positive-pole interpretation,
point increment and residue-field quotient still remain separate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

/-- The ACTUAL original-base constants commute with the canonical dual
evaluation. The scalar is the independently given pi-induced section,
and the evaluation is the previously constructed literal component map. -/
theorem internalHomDualEvaluation_originalBaseConstant
    {X : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K))
    (M : X.Modules) (U : X.Opens) (c : K)
    (m : M.val.obj (op U))
    (a : (SchemeModuleInternalHom.dual M).val.obj (op U)) :
    SchemeModuleInternalHom.evaluationBilinear M
        (SheafOfModules.unit X.ringCatSheaf) U (schemeOpenBaseRingHom pi U c • m) a =
      @HMul.hMul (Γ(X, U)) (Γ(X, U)) (Γ(X, U))
        (inferInstance : HMul (Γ(X, U)) (Γ(X, U)) (Γ(X, U)))
        (schemeOpenBaseRingHom pi U c)
        (a.1.app (op (Over.mk (𝟙 U))) m) := by
  exact a.2 (Over.mk (𝟙 U)) (schemeOpenBaseRingHom pi U c) m

variable [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct raw evaluation invertibility and the LITERAL section-dual
value law before any original projective-normalization point is inserted. -/
private theorem nativeEvaluationChartPackage004
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((SchemeModuleInternalHom.evaluationPresheaf M
      (SheafOfModules.unit X.ringCatSheaf)).app (op U)) ∧
      ∃ E : (SchemeModuleInternalHom.dual M).val.obj (op U) ≃ₗ[Γ(X, U)]
          Module.Dual (Γ(X, U)) (M.val.obj (op U)),
        ∀ (a : (SchemeModuleInternalHom.dual M).val.obj (op U))
          (m : M.val.obj (op U)), E a m = a.1.app (op (Over.mk (𝟙 U))) m := by
  refine ⟨SchemeModuleInternalHom.evaluationPresheaf_app_isIso M U e,
    SchemeModuleInternalHom.sectionDualLinearEquiv M U e, ?_⟩
  intro a m
  rfl

/-- Derive the over-site unit chart from the ORIGINAL section-induced
isomorphism at variable Scheme/M/U; construct evaluation conclusions there. -/
private theorem nativeEvaluationChartFromSectionIso004
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U))
    (hm : IsIso (schemeModuleSectionOnOpenHom M U m)) :
    IsIso ((SchemeModuleInternalHom.evaluationPresheaf M
      (SheafOfModules.unit X.ringCatSheaf)).app (op U)) ∧
      ∃ E : (SchemeModuleInternalHom.dual M).val.obj (op U) ≃ₗ[Γ(X, U)]
          Module.Dual (Γ(X, U)) (M.val.obj (op U)),
        ∀ (a : (SchemeModuleInternalHom.dual M).val.obj (op U))
          (m : M.val.obj (op U)), E a m = a.1.app (op (Over.mk (𝟙 U))) m := by
  letI := hm
  let e : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅ M.restrict U.ι :=
    asIso (schemeModuleSectionOnOpenHom M U m)
  let eOver := ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U e.symm
  let eOriginal : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U :=
    eOver ≪≫ (SchemeModuleInternalHom.unitOverIso U).symm
  exact nativeEvaluationChartPackage004 M U eOriginal

/-- Ordinary variable-scheme section chart: only the actual section-induced
isomorphism is retained from the richer geometric generator witness. -/
private def nativeSectionUnitChartExists005
    (X : Scheme.{u}) (M : X.Modules) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ m : M.val.obj (op U.1),
    IsIso (schemeModuleSectionOnOpenHom M U.1 m)

/-- Existential assembly occurs before the original normalization is inserted. -/
private theorem nativeEvaluationChartFromExists005
    {X : Scheme.{u}} (M : X.Modules) (x : X)
    (h : nativeSectionUnitChartExists005 X M x) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      IsIso ((SchemeModuleInternalHom.evaluationPresheaf M
        (SheafOfModules.unit X.ringCatSheaf)).app (op U.1)) ∧
      ∃ E : (SchemeModuleInternalHom.dual M).val.obj (op U.1) ≃ₗ[Γ(X, U.1)]
          Module.Dual (Γ(X, U.1)) (M.val.obj (op U.1)),
        ∀ (a : (SchemeModuleInternalHom.dual M).val.obj (op U.1))
          (m : M.val.obj (op U.1)), E a m = a.1.app (op (Over.mk (𝟙 U.1))) m := by
  obtain ⟨U, hxU, m, hm⟩ := h
  exact ⟨U, hxU, nativeEvaluationChartFromSectionIso004 (X := X) M U.1 m hm⟩

/-- Extract the ordinary chart from the full regular/principal original
closed-point witness, while Scheme X and point P remain variable. -/
private theorem nativeClosedPointSectionChartExtract005
    (X : Scheme.{u}) (P : closedPoints X) (x : X)
    (h :
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
      ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ m : M.val.presheaf.obj (op U.1),
        IsIso (schemeModuleSectionOnOpenHom M U.1 m) ∧
        let z : Γ(X, U.1) :=
          (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
        IsRegular z ∧ i.ker.ideal U = Ideal.span ({z} : Set Γ(X, U.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    nativeSectionUnitChartExists005 X M x := by
  dsimp only at h ⊢
  obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ := h
  exact ⟨U, hxU, m, hm⟩

/-- Capture the genuine original geometric producer with its inferred type. -/
private def originalRankOneChartEvidence005


    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :=
  projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    (K := K) p q hp hp0 n hn hq hnot

/-- One original specialization of the variable closed-point extraction.
All affine opens, generators and isomorphisms remain internally derived. -/
private def originalPointSectionChart005


    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :=
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  fun (P : closedPoints N) (x : N) =>
    nativeClosedPointSectionChartExtract005 N P x
      (originalRankOneChartEvidence005 (K := K) p q hp hp0 n hn hq hnot P x)

/-- Actual pointwise specialization: EVERY chart section and its IsIso
come from the accepted ORIGINAL geometric rank-one theorem internally. -/
private theorem originalPointEvaluationCharts004

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
      ∃ U : N.affineOpens, x ∈ U.1 ∧
        IsIso ((SchemeModuleInternalHom.evaluationPresheaf M
          (SheafOfModules.unit N.ringCatSheaf)).app (op U.1)) ∧
        ∃ E : (SchemeModuleInternalHom.dual M).val.obj (op U.1) ≃ₗ[Γ(N, U.1)]
          Module.Dual (Γ(N, U.1)) (M.val.obj (op U.1)),
          ∀ (a : (SchemeModuleInternalHom.dual M).val.obj (op U.1))
            (m : M.val.obj (op U.1)),
            E a m = a.1.app (op (Over.mk (𝟙 U.1))) m := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P x
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  exact nativeEvaluationChartFromExists005 (X := N) M x
    (originalPointSectionChart005 (K := K) p q hp hp0 n hn hq hnot P x)

/-- EVERY point has an affine chart on which the CONSTRUCTED global
O-linear dual really has the original ring-linear dual sections, and
the SAME canonical raw tensor evaluation is invertible. All point-ideal
charts are internally derived from the primitive original geometry. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_dual_evaluation_charts
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
      ∃ U : N.affineOpens, x ∈ U.1 ∧
        IsIso ((SchemeModuleInternalHom.evaluationPresheaf M
          (SheafOfModules.unit N.ringCatSheaf)).app (op U.1)) ∧
        ∃ E : (SchemeModuleInternalHom.dual M).val.obj (op U.1) ≃ₗ[Γ(N, U.1)]
          Module.Dual (Γ(N, U.1)) (M.val.obj (op U.1)),
          ∀ (a : (SchemeModuleInternalHom.dual M).val.obj (op U.1))
            (m : M.val.obj (op U.1)),
            E a m = a.1.app (op (Over.mk (𝟙 U.1))) m := by
  exact originalPointEvaluationCharts004 (K := K) p q hp hp0 n hn hq hnot

/-- The SAME actual closed-point ideal has the CONSTRUCTED actual global
O-linear dual as its genuine tensor inverse. Invertibility of its SAME
canonical evaluation is proved internally from primitive geometry.
No locally-free, dual-comparison or evaluation certificate is supplied. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_dualEvaluation_isIso
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
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      IsIso (SchemeModuleInternalHom.dualEvaluation M) := by
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
  let U : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hU (x : N) : x ∈ (U x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.obj (op (U x).1) :=
    Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (U x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  apply SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts
    M (fun x => (U x).1) hU
  intro x
  letI := hm x
  let e : SheafOfModules.unit ((U x).1 : Scheme.{u}).ringCatSheaf ≅
      M.restrict (U x).1.ι := asIso (schemeModuleSectionOnOpenHom M (U x).1 (m x))
  exact (ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (U x).1 e.symm) ≪≫
    (SchemeModuleInternalHom.unitOverIso (U x).1).symm

end PfaffianDescent.Coray
