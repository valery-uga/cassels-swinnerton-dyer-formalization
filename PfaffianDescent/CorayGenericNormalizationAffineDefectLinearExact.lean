import PfaffianDescent.CorayNormalizationHomGroundAffineDefect
import PfaffianDescent.CorayGenericNormalizationLowDegreeLinearExact
import Mathlib.Algebra.Module.Submodule.Range

/-! The SAME canonical normalization connecting map on the actual chosen
affine defect, retaining the actual global projection contribution.
No finite-dimensionality, constants equality, genus or RR assertion.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

/-- A name for the EXISTING actual affine integral-closure defect with the
original pi-induced ring map and scalar restriction. No action is replaced. -/
abbrev GenericNormalizationAffineDefectOver
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) [Nonempty U] : ModuleCat K :=
  let beta : K →+* Γ(X, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  (ModuleCat.restrictScalars beta).obj
    (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField))

/-- The SAME actual global cokernel projection followed by the genuine
Hom-to-chosen-affine-defect equivalence. Its image is retained in the LES. -/
def genericNormalizationAffineDefectProjectionLinearMap
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)) →ₗ[K]
      GenericNormalizationAffineDefectOver X pi U := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact (genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU).toLinearMap.comp
    (genericNormalizationHomQuotientLinearMap X pi)

/-- The SAME actual connecting class of the canonical normalization short
exact sequence, applied through the genuine affine-defect equivalence inverse.
No extension class or connecting-map compatibility is supplied as a premise. -/
def genericNormalizationAffineDefectConnectingLinearMap
    (X : Scheme.{u}) [IsIntegral X] [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    GenericNormalizationAffineDefectOver X pi U →ₗ[K]
      schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact (genericNormalizationHomConnectingLinearMap X pi).comp
    (genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU).symm.toLinearMap

/-- The left map still evaluates the SAME literal original cokernel
projection. This global-section contribution is not discarded or set to zero. -/
theorem genericNormalizationAffineDefectProjectionLinearMap_apply
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf),
      genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U hU hsU s =
        genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU
          (s ≫ cokernel.π (genericNormalizationUnitToPushforwardUnit X)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact fun _ ↦ rfl

/-- The actual connecting map on D has exactly the original canonical
Hom connecting value on the constructed inverse section. -/
theorem genericNormalizationAffineDefectConnectingLinearMap_apply
    (X : Scheme.{u}) [IsIntegral X] [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ d : GenericNormalizationAffineDefectOver X pi U,
      genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U hU hsU d =
        genericNormalizationHomConnectingLinearMap X pi
          ((genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU).symm d) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact fun _ ↦ rfl

/-- Genuine exactness at actual D and actual H¹_X(O_X), both actual
K-submodule kernel/range equalities, and surjection onto intrinsic H¹_N(O_N).
Every original LES/comparison/Q Ext input is derived by the existing sources;
only ordinary geometry and actual support-contained-in-affine hypotheses remain. -/
theorem genericNormalizationAffineDefect_lowDegree_exact_surjective_and_kernels
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
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
    let σ := genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U hU hsU
    let δ := genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U hU hsU
    let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
    Function.Exact σ δ ∧ Function.Exact δ g ∧
      δ.ker = LinearMap.range σ ∧ g.ker = LinearMap.range δ ∧ Function.Surjective g := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  let E := genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU
  let σ := genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U hU hsU
  let δ := genericNormalizationAffineDefectConnectingLinearMap X pi hclosed U hU hsU
  let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
  have hOriginal := (genericNormalization_lowDegreeLinearMaps_exact X pi).1
  have hIntrinsic := (genericNormalization_connecting_intrinsicCohomologyOne_exact_and_kernel X pi).1
  have hD : Function.Exact σ δ := by
    intro d
    change genericNormalizationHomConnectingLinearMap X pi (E.symm d) = 0 ↔
      ∃ s, E (genericNormalizationHomQuotientLinearMap X pi s) = d
    constructor
    · intro hd
      obtain ⟨s, hs⟩ := (hOriginal (E.symm d)).mp hd
      exact ⟨s, (congrArg E hs).trans (E.apply_symm_apply d)⟩
    · rintro ⟨s, hs⟩
      apply (hOriginal (E.symm d)).mpr
      refine ⟨s, ?_⟩
      simpa only [E.symm_apply_apply] using congrArg E.symm hs
  have hH : Function.Exact δ g := by
    intro z
    change g z = 0 ↔ ∃ d, genericNormalizationHomConnectingLinearMap X pi (E.symm d) = z
    constructor
    · intro hz
      obtain ⟨s, hs⟩ := (hIntrinsic z).mp hz
      refine ⟨E s, ?_⟩
      simpa only [E.symm_apply_apply] using hs
    · rintro ⟨d, hd⟩
      exact (hIntrinsic z).mpr ⟨E.symm d, hd⟩
  refine ⟨hD, hH, ?_, ?_, ?_⟩
  · apply Submodule.ext
    intro d
    change δ d = 0 ↔ ∃ s, σ s = d
    exact hD d
  · apply Submodule.ext
    intro z
    change g z = 0 ↔ ∃ d, δ d = z
    exact hH z
  · exact genericNormalization_intrinsicCohomologyOneLinearMap_surjective_of_closedSupport_subset_affine
      X pi hclosed U hU hsU

end PfaffianDescent.Coray
