import PfaffianDescent.CorayPerfectNormalizationCohomologyOneLinearComparison
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact

/-! SOURCE ONLY / UNVERIFIED. SAME actual normalization inclusion followed
by SAME native intrinsic comparison, linear for original pi and nu>>pi.
Closed-support/actual-affine geometry derives actual surjectivity; no
H1-finite, genus, constants, or Ext-vanishing conclusion is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

def perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap
    [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[K]
      schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  exact (perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi).toLinearMap.comp
    (schemeModuleCohomologyLinearMapOver pi (genericNormalizationUnitToPushforwardUnit X) 1)

/-- Explicit identity with the original inclusion-induced additive map
followed by the previously constructed actual normalization comparison. -/
theorem perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap_apply
    [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    ∀ z : schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1,
      perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi z =
        perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
          (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) := by
  exact fun z => rfl

theorem perfectField_genericNormalization_intrinsicCohomologyOneLinearMap_surjective_of_closedSupport_subset_affine
    [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U)
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    Function.Surjective (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  let E := perfectField_genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
  have hsurj := genericNormalization_cohomologyOneMap_surjective_of_closedSupport_subset_affine
    X pi hclosed U hU hsU
  change Function.Surjective (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi)
  intro y
  obtain ⟨z, hz⟩ := hsurj (E.symm y)
  refine ⟨z, ?_⟩
  change E (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) = y
  rw [hz, E.apply_symm_apply]

end PfaffianDescent.Coray
