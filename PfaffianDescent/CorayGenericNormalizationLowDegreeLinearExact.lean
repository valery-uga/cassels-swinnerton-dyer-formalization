import PfaffianDescent.CorayGenericNormalizationLowDegreeExact
import PfaffianDescent.CorayNormalizationCohomologyOneLinearComparison
import Mathlib.Algebra.Module.Submodule.Range

/-! The SAME actual normalization low-degree maps over the original field.
All Hom and Ext actions are induced by actual pi, and intrinsic normalization
cohomology uses actual nu ≫ pi. No constants/dimension/genus conclusion.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

/-- The SAME actual coefficient-induced cohomology map is linear for the
actual pi-induced Hom category and its installed Ext action. -/
def schemeModuleCohomologyLinearMapOver {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleCohomology X M n →ₗ[K] schemeModuleCohomology X N n := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine { toAddHom := (schemeModuleCohomologyMap X f n).toAddHom, map_smul' := ?_ }
  intro c z
  change (c • z).comp (Ext.mk₀ f) (add_zero n) =
    c • z.comp (Ext.mk₀ f) (add_zero n)
  exact Ext.smul_comp z (Ext.mk₀ f) (add_zero n) c

/-- The literal canonical cokernel projection induces the original Hom
map, now linear for actual pi. The target is the ACTUAL global quotient Q. -/
def genericNormalizationHomQuotientLinearMap
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)) →ₗ[K]
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact CategoryTheory.Linear.rightComp K
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    (cokernel.π (genericNormalizationUnitToPushforwardUnit X))

/-- The SAME actual connecting AddHom from the literal canonical cokernel
extension class is linear. ShortExact is proved by the existing unit-mono
construction; no chosen extension or compatibility certificate is supplied. -/
def genericNormalizationHomConnectingLinearMap
    (X : Scheme.{u}) [IsIntegral X] [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X) →ₗ[K]
    schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let hS := genericNormalization_cokernelSequence_shortExact X
  refine { toAddHom := (genericNormalizationHomConnecting X).toAddHom, map_smul' := ?_ }
  intro c s
  change (Ext.mk₀ (c • s)).comp hS.extClass (show 0 + 1 = 1 by rfl) =
    c • (Ext.mk₀ s).comp hS.extClass (show 0 + 1 = 1 by rfl)
  rw [Ext.mk₀_smul, Ext.smul_comp]

/-- Actual linear low-degree normalization maps are exact at Hom(O_X,Q)
and H¹_X(O_X), with the SAME actual additive maps as the prior source. -/
theorem genericNormalization_lowDegreeLinearMaps_exact
    (X : Scheme.{u}) [IsIntegral X] [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Function.Exact (genericNormalizationHomQuotientLinearMap X pi)
      (genericNormalizationHomConnectingLinearMap X pi) ∧
    Function.Exact (genericNormalizationHomConnectingLinearMap X pi)
      (schemeModuleCohomologyLinearMapOver pi (genericNormalizationUnitToPushforwardUnit X) 1) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact ⟨genericNormalization_homQuotient_connecting_exact X,
    genericNormalization_connecting_cohomologyOne_exact X⟩

/-- The canonical original inclusion map followed by the SAME actual
intrinsic normalization comparison, for actual pi/composite scalar actions.
Native Ext infrastructure and finite-normalization inputs are internal. -/
def genericNormalizationCohomologyOneToNormalizationLinearMap
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
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
  exact (genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi).toLinearMap.comp
    (schemeModuleCohomologyLinearMapOver pi (genericNormalizationUnitToPushforwardUnit X) 1)

/-- Explicit identity with the original inclusion-induced additive map
followed by the previously constructed actual normalization comparison. -/
theorem genericNormalizationCohomologyOneToNormalizationLinearMap_apply
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
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
      genericNormalizationCohomologyOneToNormalizationLinearMap X pi z =
        genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
          (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) := by
  exact fun z => rfl

/-- Passing to intrinsic normalization H¹ preserves the exact connecting
image. The equality is of the actual K-submodule kernel and actual range;
no closed-support, constants or dimension hypothesis is needed. -/
theorem genericNormalization_connecting_intrinsicCohomologyOne_exact_and_kernel
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
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
    Function.Exact (genericNormalizationHomConnectingLinearMap X pi)
      (genericNormalizationCohomologyOneToNormalizationLinearMap X pi) ∧
    (genericNormalizationCohomologyOneToNormalizationLinearMap X pi).ker =
      LinearMap.range (genericNormalizationHomConnectingLinearMap X pi) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  let E := genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
  have hex : Function.Exact (genericNormalizationHomConnectingLinearMap X pi)
      (genericNormalizationCohomologyOneToNormalizationLinearMap X pi) := by
    intro z
    change E (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) = 0 ↔
      ∃ s, genericNormalizationHomConnecting X s = z
    rw [← E.map_zero, E.injective.eq_iff]
    exact genericNormalization_connecting_cohomologyOne_exact X z
  refine ⟨hex, ?_⟩
  ext z
  change genericNormalizationCohomologyOneToNormalizationLinearMap X pi z = 0 ↔
    ∃ s, genericNormalizationHomConnectingLinearMap X pi s = z
  exact hex z

/-- The actual map onto intrinsic normalization H¹ is surjective when the
ACTUAL Q stalk support is closed and contained in an ACTUAL affine open.
All local Q/QC/Ext/cover/image inputs are internally derived by the genuine
global-Q source; no vanishing or comparison certificate is supplied. -/
theorem genericNormalization_intrinsicCohomologyOneLinearMap_surjective_of_closedSupport_subset_affine
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
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
    Function.Surjective (genericNormalizationCohomologyOneToNormalizationLinearMap X pi) := by
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
  let E := genericNormalizationPushforwardUnit_cohomologyOneLinearEquiv X pi
  have hsurj := genericNormalization_cohomologyOneMap_surjective_of_closedSupport_subset_affine
    X pi hclosed U hU hsU
  change Function.Surjective (genericNormalizationCohomologyOneToNormalizationLinearMap X pi)
  intro y
  obtain ⟨z, hz⟩ := hsurj (E.symm y)
  refine ⟨z, ?_⟩
  change E (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z) = y
  rw [hz, E.apply_symm_apply]

end PfaffianDescent.Coray
