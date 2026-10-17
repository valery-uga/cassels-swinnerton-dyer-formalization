import PfaffianDescent.CorayNormalizationFiniteExactRank
import PfaffianDescent.CorayPerfectNormalizationLowDegreeRankExact
import PfaffianDescent.CorayPerfectOwnUnitH1Finite
import PfaffianDescent.CorayPerfectOwnNormalizationH1LinearSurjection
import PfaffianDescent.CorayPerfectNormalizationFullConstantsHZeroRank
import PfaffianDescent.SchemeModuleUnitHomGroundSections

/-! Actual full Euler comparison for SAME selected C/N/Q over original perfectK.
All finiteness and surjectivity inputs are constructed internally. Neither
constants field is replaced by K. No numerical genus claim. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u

open AllCharacteristics.HomogeneousProjective
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem selectedComponent_actualNormalizationH1_rank_correction
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    let pi := toBase C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
    letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
    letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
    let Q : X.Modules := genericNormalizationQuotientSheaf X
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (schemeModuleCohomology X OX 1) +
      Module.finrank K (LinearMap.range σ) =
      Module.finrank K (schemeModuleCohomology N ON 1) +
      Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
  letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
  letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
  let Q : X.Modules := genericNormalizationQuotientSheaf X
  let σ := genericNormalizationHomQuotientLinearMap X pi
  let δ := genericNormalizationHomConnectingLinearMap X pi
  letI : LocallyOfFiniteType pi := inferInstance
  let g := perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi
  letI : Module.Finite K (schemeModuleCohomology X OX 1) :=
    perfectField_selectedProjectivePrimeComponent_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot C hIC hprime P
  letI : Module.Finite K (SchemeModuleGlobalSectionsOver pi Q) :=
    (perfectField_selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hIC hprime P).1
  let eQ := schemeModuleUnitHomGroundLinearEquivGlobalSections pi Q
  letI : Module.Finite K (OX ⟶ Q) := Module.Finite.equiv eQ.symm
  have hσδ : Function.Exact σ δ := (genericNormalization_lowDegreeLinearMaps_exact X pi).1
  have hδg : Function.Exact δ g :=
    perfectField_genericNormalization_connecting_intrinsicCohomologyOne_exact X pi
  have hg : Function.Surjective g :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_intrinsicCohomologyOneLinearMap_surjective
      p q hp hp0 n hq hnot C hIC hprime P
  have h := normalization_finiteExact_rank_correction σ δ g hσδ hδg hg
  exact h.trans (congrArg (fun t : ℕ =>
    Module.finrank K (schemeModuleCohomology N ON 1) + t) eQ.finrank_eq)

/-- Original-K Euler correction for SAME selected C, actual normalization N,
and full actual Q. Genuine positive vanishing/descent derives source finiteH1;
actual support geometry derives finiteQ/normalizationH1 surjection; BOTH full
constants ranks and SAME canonical projection image are retained and cancel.
No finite-H1, desired vanishing, support, comparison or genus bound is input. -/
theorem perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    let pi := toBase C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
    letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
    letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
    let Q : X.Modules := genericNormalizationQuotientSheaf X
    (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) : ℤ) -
      (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi OX ⊤) : ℤ) -
      (Module.finrank K (schemeModuleCohomology X OX 1) : ℤ) +
      (Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) : ℤ) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
  letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
  letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
  let Q : X.Modules := genericNormalizationQuotientSheaf X
  letI : IsProper pi := isProper_toBase C
  have h0 := perfectField_integralProper_genericNormalization_unit_topSections_finrank_eq_curveRank_add_globalProjectionImage X pi
  have h1 := selectedComponent_actualNormalizationH1_rank_correction
    p q hp hp0 n hq hnot C hIC hprime P
  exact normalization_fullConstants_euler_of_rank_correction _ _ _ _ _ _ h0 h1

end PfaffianDescent.Coray
