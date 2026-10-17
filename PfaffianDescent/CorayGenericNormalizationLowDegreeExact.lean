import PfaffianDescent.CorayGenericNormalizationUnitMono
import PfaffianDescent.CorayGenericNormalizationGlobalExtOne
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Actual low-degree exactness for the canonical normalization sequence.
The connecting map is built from the literal cokernel extension class.
The target Ext group is on the original scheme and has the ACTUAL
normalization pushforward as second argument. No comparison with cohomology
on the normalization, dimension formula, or genus conclusion is asserted.
STATUS: UNVERIFIED SOURCE ONLY. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL connecting map from Hom(O_X,Q) to Ext¹(O_X,O_X), using the
extension class of the ACTUAL canonical normalization cokernel sequence. -/
def genericNormalizationHomConnecting
    (X : Scheme.{u}) [IsIntegral X] [hExt : HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X) →+
      schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let hS := genericNormalization_cokernelSequence_shortExact X
  exact
    { toFun := fun s => (Ext.mk₀ s).comp hS.extClass (show 0 + 1 = 1 by rfl)
      map_zero' := by rw [Ext.mk₀_zero, Ext.zero_comp]
      map_add' := fun s t => by rw [Ext.mk₀_add, Ext.add_comp] }

/-- The original Hom map induced by the actual quotient projection and the
actual connecting map are exact at Hom(O_X,Q). No exactness premise occurs. -/
theorem genericNormalization_homQuotient_connecting_exact
    (X : Scheme.{u}) [IsIntegral X] [hExt : HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
    Function.Exact (fun s : S.X₁ ⟶ S.X₂ => s ≫ S.g)
      (genericNormalizationHomConnecting X) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  change Function.Exact (fun s : S.X₁ ⟶ S.X₂ => s ≫ S.g)
    (genericNormalizationHomConnecting X)
  intro s
  constructor
  · intro hs
    have hs' : (Ext.mk₀ s).comp hS.extClass (show 0 + 1 = 1 by rfl) = 0 := hs
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ O hS (Ext.mk₀ s)
      (show 0 + 1 = 1 by rfl) hs'
    refine ⟨Ext.addEquiv₀ t, ?_⟩
    apply (Ext.mk₀_bijective O S.X₃).1
    rw [← Ext.mk₀_comp_mk₀]
    have hmk : Ext.mk₀ (Ext.addEquiv₀ t) = t := Ext.mk₀_addEquiv₀_apply t
    have hpost := congrArg
      (fun w : Ext.{u} (C := X.Modules) O S.X₂ 0 =>
        w.comp (Ext.mk₀ S.g) (zero_add 0)) hmk
    exact hpost.trans ht
  · rintro ⟨t, rfl⟩
    change (Ext.mk₀ (t ≫ S.g)).comp hS.extClass (show 0 + 1 = 1 by rfl) = 0
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero]

/-- The actual connecting map and the Ext¹ map induced by the ACTUAL
canonical inclusion are exact at Ext¹(O_X,O_X), on every integral X. -/
theorem genericNormalization_connecting_cohomologyOne_exact
    (X : Scheme.{u}) [IsIntegral X] [hExt : HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    Function.Exact (genericNormalizationHomConnecting X)
      (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  intro z
  constructor
  · intro hz
    have hz' : z.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := hz
    obtain ⟨s, hs⟩ := Ext.covariant_sequence_exact₁ O hS z hz'
      (show 0 + 1 = 1 by rfl)
    refine ⟨Ext.addEquiv₀ s, ?_⟩
    change (Ext.mk₀ (Ext.addEquiv₀ s)).comp hS.extClass
      (show 0 + 1 = 1 by rfl) = z
    simpa only [Ext.mk₀_addEquiv₀_apply] using hs
  · rintro ⟨s, rfl⟩
    change ((Ext.mk₀ s).comp hS.extClass (show 0 + 1 = 1 by rfl)).comp
      (Ext.mk₀ S.f) (add_zero 1) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

/-- The kernel of the ACTUAL inclusion-induced Ext¹ map is exactly the
additive image of the ACTUAL connecting map from Hom(O_X,Q). -/
theorem genericNormalization_cohomologyOne_ker_eq_connecting_range
    (X : Scheme.{u}) [IsIntegral X] [hExt : HasExt.{u} X.Modules] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1).ker =
      (genericNormalizationHomConnecting X).range := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  ext z
  change schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1 z = 0 ↔
    ∃ s, genericNormalizationHomConnecting X s = z
  exact genericNormalization_connecting_cohomologyOne_exact X z

/-- The ACTUAL inclusion induces a surjection from Ext¹(O_X,O_X) onto
Ext¹(O_X,nu_*O_normalization) when the ACTUAL quotient's closed support is
contained in an ACTUAL affine open. Quotient Ext¹ vanishing and every
short-exactness input are derived internally from those geometric inputs. -/
theorem genericNormalization_cohomologyOneMap_surjective_of_closedSupport_subset_affine
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U)
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    Function.Surjective
      (schemeModuleCohomologyMap X (genericNormalizationUnitToPushforwardUnit X) 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : Subsingleton (schemeModuleCohomology X (genericNormalizationQuotientSheaf X) 1) :=
    genericNormalizationQuotientSheaf_cohomology_one_subsingleton_of_closedSupport_subset_affine
      X pi hclosed U hU hsU
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let S := ShortComplex.cokernelSequence (genericNormalizationUnitToPushforwardUnit X)
  have hS : S.ShortExact := genericNormalization_cokernelSequence_shortExact X
  letI : Subsingleton (Ext.{u} (C := X.Modules) O S.X₃ 1) := by
    change Subsingleton (schemeModuleCohomology X (genericNormalizationQuotientSheaf X) 1)
    infer_instance
  intro z
  have hz : z.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := Ext.covariant_sequence_exact₂ O hS z hz
  exact ⟨s, hs⟩

end PfaffianDescent.Coray
