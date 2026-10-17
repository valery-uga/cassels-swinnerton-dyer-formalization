import PfaffianDescent.CorayNormalizationGlobalUnitSectionsFinite
import PfaffianDescent.CorayNormalizationClosedPointIncrementCohomology
import PfaffianDescent.SchemeModuleInternalHomRestrictedFiberIso
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! The actual point increment over original K has weighted fiber dimension
and the genuine five-term Euler balance. All frames, outer finiteness,
exactness, injectivity, surjectivity and native Ext infrastructure are internal
to the primitive p/q callers. Normalization global constants are retained in
full; no equality with K, divisor/pole comparison or RR is concluded.
The canonical-fiber/cohomology/curve-constants dependencies remain UNVERIFIED.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual chosen frame of the SAME intrinsic dual fiber. The regular
ideal chart is proved internally; the identification with the bare residue
field is choice dependent, while the intrinsic fiber remains canonical. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualFiber_nonempty_unitIso
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      Nonempty ((Scheme.Modules.pullback i).obj D ≅
        SheafOfModules.unit (Spec (N.residueField P.1)).ringCatSheaf) := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  obtain ⟨U, hPU, m, hm, _hregular, _hprincipal⟩ :=
    projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
      p q hp hp0 n hn hq hnot P P.1
  letI := hm
  let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
    asIso (schemeModuleSectionOnOpenHom M U.1 m)
  let eOver : M.over U.1 ≅ (SheafOfModules.unit N.ringCatSheaf).over U.1 :=
    ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm
  let eD := SchemeModuleInternalHom.dualRestrictUnitIso U.1 eOver
  have hrange : Set.range i ⊆ Set.range U.1.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hPU⟩, rfl⟩
  let j := IsOpenImmersion.lift U.1.ι i hrange
  have hji : j ≫ U.1.ι = i := IsOpenImmersion.lift_fac _ _ _
  have hframe := schemeModuleFiberFrameIso U.1.ι j D eD
  exact ⟨by simpa only [hji] using hframe⟩

/-- Finite actual supported fiber sections and their FULL residue degree.
Finite normalization, finite-type composition and the actual chosen frame
are all constructed internally; no dimension or scalar certificate occurs. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualFiber_topSections_finite_and_finrank
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      let F := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D)
      Module.Finite K (SchemeModuleOpenSectionsOver pi F ⊤) ∧
        Module.finrank K (SchemeModuleOpenSectionsOver pi F ⊤) = pi.residueDegree P.1 := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  obtain ⟨e⟩ := projectiveIntersection_genericNormalization_closedPoint_dualFiber_nonempty_unitIso
    p q hp hp0 n hn hq hnot P
  exact schemeModuleResiduePointFiberTop_finite_and_finrank pi P D e

/-- The genuine five-term Euler balance for SAME O_N -> D_P -> i_*i^*D_P.
It proves finite sections of D_P and finite intrinsic H1(D_P), retaining
the full actual normalization H0 and the full canonical projection image. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_finite_and_euler_balance
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      Module.Finite K (SchemeModuleOpenSectionsOver pi D ⊤) ∧
        Module.Finite K (schemeModuleCohomology N D 1) ∧
        Module.finrank K (SchemeModuleOpenSectionsOver pi D ⊤) +
            Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) =
          Module.finrank K (SchemeModuleOpenSectionsOver pi (SheafOfModules.unit N.ringCatSheaf) ⊤) +
            pi.residueDegree P.1 + Module.finrank K (schemeModuleCohomology N D 1) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    projectiveIntersection_genericNormalization_unit_topSections_finite_native
      p q hp hp0 n hn hq hnot
  have hUnitH1Finite :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot
  letI : Module.Finite K (schemeModuleCohomology N O 1) := hUnitH1Finite
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  let delta := SchemeModuleInternalHom.unitToHom j
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D
  let F := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D)
  let S := SchemeModuleInternalHom.incrementCokernelSequence j
  let hS := projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
    p q hp hp0 n hn hq hnot P
  letI : Module.Finite K (schemeModuleCohomology N S.X₁ 1) := by
    change Module.Finite K (schemeModuleCohomology N O 1)
    exact hUnitH1Finite
  letI : Mono delta := by
    change Mono S.f
    exact hS.mono_f
  have hFiberData :=
    projectiveIntersection_genericNormalization_closedPoint_dualFiber_topSections_finite_and_finrank
      p q hp hp0 n hn hq hnot P
  have hfiniteF := hFiberData.1
  have hdimF := hFiberData.2
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi F ⊤) := hfiniteF
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj D) ⊤) := by
    change Module.Finite K (SchemeModuleOpenSectionsOver pi F ⊤)
    exact hfiniteF
  have hdimEta : Module.finrank K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj D) ⊤) =
      pi.residueDegree P.1 := by
    change Module.finrank K (SchemeModuleOpenSectionsOver pi F ⊤) = pi.residueDegree P.1
    exact hdimF
  have hLES :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_globalSections_cohomology_exact
      p q hp hp0 n hn hq hnot P
  let E := Classical.choose hLES
  have hExact := (Classical.choose_spec hLES).2
  have hex0 := hExact.1
  have hex1 := hExact.2.1
  have hex2 := hExact.2.2.1
  have hsurj := hExact.2.2.2.2
  let b := (schemeModuleOpenTopConnectingLinearMapOver pi S hS).comp
    (schemeModuleOpenTopCoefficientLinearMapOver pi E.inv)
  have hrank := finiteFiveTermLinearRank
    (schemeModuleOpenTopCoefficientLinearMapOver pi delta)
    (schemeModuleOpenTopCoefficientLinearMapOver pi eta) b
    (schemeModuleCohomologyLinearMapOver pi delta 1)
    (schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi delta)
    hex0 hex1 hex2 hsurj
  have hrankLocal :
      Module.finrank K (SchemeModuleOpenSectionsOver pi D ⊤) +
          Module.finrank K (schemeModuleCohomology N O 1) =
        Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi
            ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj D) ⊤) +
          Module.finrank K (schemeModuleCohomology N D 1) := hrank.2.2
  refine ⟨hrank.1, hrank.2.1, ?_⟩
  change Module.finrank K (SchemeModuleOpenSectionsOver pi D ⊤) +
      Module.finrank K (schemeModuleCohomology N O 1) =
    Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) +
      pi.residueDegree P.1 + Module.finrank K (schemeModuleCohomology N D 1)
  exact hrankLocal.trans (congrArg (fun d : ℕ =>
    Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) + d +
      Module.finrank K (schemeModuleCohomology N D 1)) hdimEta)

/-- The literal integer H0-minus-H1 point increment. This is the
consequence of the same finite five-term sequence; no higher-degree Euler
convergence, divisor interpretation or normalization constants equality is
silently supplied by this low-degree statement. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_h0_minus_h1_increment
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      (Module.finrank K (SchemeModuleOpenSectionsOver pi D ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology N D 1) =
        (Module.finrank K (SchemeModuleOpenSectionsOver pi (SheafOfModules.unit N.ringCatSheaf) ⊤) : ℤ) -
          Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
          pi.residueDegree P.1 := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  have h := (projectiveIntersection_genericNormalization_closedPoint_dualIncrement_finite_and_euler_balance
    p q hp hp0 n hn hq hnot P).2.2
  have hi : (Module.finrank K (SchemeModuleOpenSectionsOver pi D ⊤) : ℤ) +
      Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi (SheafOfModules.unit N.ringCatSheaf) ⊤) : ℤ) +
        pi.residueDegree P.1 + Module.finrank K (schemeModuleCohomology N D 1) := by
    exact_mod_cast h
  omega

end PfaffianDescent.Coray
