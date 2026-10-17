import PfaffianDescent.CorayPerfectGenericNormalizationH1LinearSurjection
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact

/-! Exactness for SAME perfect-K intrinsic normalization H1 map, independently
of H1 finiteness or genus. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u

/-- The actual original-pi connecting map followed by SAME perfect-field
intrinsic normalization H1 map is exact. Only the already constructed actual
linear normalization comparison is used; no comparison is supplied. -/
theorem perfectField_genericNormalization_connecting_intrinsicCohomologyOne_exact
    {K : Type u} [Field K] [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
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
    Function.Exact (genericNormalizationHomConnectingLinearMap X pi)
      (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi) := by
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
  let E := perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
  change Function.Exact (genericNormalizationHomConnectingLinearMap X pi)
    (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi)
  intro z
  change E (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) = 0 ↔
    ∃ s, genericNormalizationHomConnecting X s = z
  rw [← E.map_zero, E.injective.eq_iff]
  exact genericNormalization_connecting_cohomologyOne_exact X z

end PfaffianDescent.Coray
