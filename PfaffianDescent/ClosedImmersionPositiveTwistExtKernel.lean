import PfaffianDescent.ExtKernelEquivalenceTransport
import PfaffianDescent.VoisinTwistEquivalenceSerreTerms
import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.SchemePushforwardUnitSections

/-! # Actual kernel transport into the positive-twist Serre sequence

The negative-twist point kernel is transported through the proved intrinsic
twist equivalence. The sequence map is the original closed-immersion map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
open IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Remove the unit-tensor presentation of the quotient, retaining its
original augmentation and its actual nonzero Ext kernel. -/
theorem closedImmersion_untwisted_exists_nonzeroExt_kernel
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [hExt : HasExt.{u} X.Modules] (N : X.Modules) (n : ℕ)
    (z : Ext.{u} (C := X.Modules)
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
      N n) (hz : z ≠ 0)
    (hkernel : (Ext.mk₀.{u} (C := X.Modules) (closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add n) = 0) :
    ∃ z' : Ext.{u} (C := X.Modules) ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) N n,
      z' ≠ 0 ∧
        (Ext.mk₀.{u} (C := X.Modules) (closedImmersionModulePushforwardSequence i).g).comp z'
          (zero_add n) = 0 := by
  exact exists_nonzero_ext_kernel_of_sourceIso.{u+1,u,u} (C := X.Modules)
    (closedImmersionModulePushforwardSequence i).g
    (closedImmersionIdealTwistSequenceUnitTargetIso i) n z hz hkernel

set_option backward.isDefEq.respectTransparency false in
/-- The actual negative-twist augmentation kernel gives a nonzero kernel
for the positively twisted ideal sequence. -/
theorem quotientPositiveTwist_exists_nonzeroExtTwo_kernel_of_untwisted
    {K : Type u} [Field K] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ)
    [hExt : HasExt.{u} (scheme I).Modules]
    (z : Ext.{u} (C := (scheme I).Modules)
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (scheme I).ringCatSheaf)).X₃
      (sheafOfModules (grading I) m) 2) (hz : z ≠ 0)
    (hkernel : (Ext.mk₀.{u} (C := (scheme I).Modules) (closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2) = 0) :
    ∃ z' : Ext.{u} (C := (scheme I).Modules)
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) m)).X₃
      (show (scheme I).Modules from SheafOfModules.unit (scheme I).ringCatSheaf) 2,
      z' ≠ 0 ∧
        (Ext.mk₀.{u} (C := (scheme I).Modules) (closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) m)).g).comp z' (zero_add 2) = 0 := by
  obtain ⟨z₀, hz₀, hker₀⟩ :=
    closedImmersion_untwisted_exists_nonzeroExt_kernel i
      (sheafOfModules (grading I) m) 2 z hz hkernel
  letI : EnoughInjectives (scheme I).Modules :=
    sheafOfModules_enoughInjectives (scheme I).ringCatSheaf
  letI : (quotientInverseTwistEquivalence I m).functor.Additive := by
    change (schemeModuleTensorRight (sheafOfModules (grading I) m)).Additive
    infer_instance
  exact exists_nonzero_ext_kernel_of_exactEquivalenceOfIsos.{u+1,u,u+1,u,u,u}
    (C := (scheme I).Modules) (D := (scheme I).Modules)
    (quotientInverseTwistEquivalence I m)
    (closedImmersionIdealTwistSequence i (positiveSheafOfModules (grading I) m)).g
    (closedImmersionModulePushforwardSequence i).g
    (quotientInverseTwistMiddleIso I i m) (quotientInverseTwistTargetIso I i m)
    (quotientInverseTwistUnitIso I m)
    (quotientInverseTwist_idealSequence_g_square I i m) 2 z₀ hz₀ hker₀

set_option backward.isDefEq.respectTransparency false in
/-- The transported class lifts to an actual nonzero Serre extension class,
whose actual connecting image is nonzero. -/
theorem quotientPositiveTwist_exists_nonzeroExtOne_of_untwisted_kernel
    {K : Type u} [Field K] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] (m : ℕ)
    [HasExt.{u} (scheme I).Modules]
    (z : Ext.{u} (C := (scheme I).Modules)
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (scheme I).ringCatSheaf)).X₃
      (sheafOfModules (grading I) m) 2) (hz : z ≠ 0)
    (hkernel : (Ext.mk₀.{u} (C := (scheme I).Modules) (closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2) = 0) :
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I m
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I m
    ∃ x : Ext.{u} (C := (scheme I).Modules)
        (closedImmersionIdealTwist i (positiveSheafOfModules (grading I) m))
        (show (scheme I).Modules from SheafOfModules.unit (scheme I).ringCatSheaf) 1,
      x ≠ 0 ∧
        (closedImmersionIdealTwistSequence_shortExact i
          (positiveSheafOfModules (grading I) m)).extClass.comp x
          (show 1 + 1 = 2 by omega) ≠ 0 := by
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I m
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I m
  obtain ⟨z', hz', hker'⟩ :=
    quotientPositiveTwist_exists_nonzeroExtTwo_kernel_of_untwisted I i m z hz hkernel
  obtain ⟨x, hx, hconnecting⟩ :=
    closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_comp_eq_zero i
      (positiveSheafOfModules (grading I) m)
      (show (scheme I).Modules from SheafOfModules.unit (scheme I).ringCatSheaf)
      z' hz' hker'
  exact ⟨x, hx, by rwa [hconnecting]⟩

end PfaffianDescent.ProjectiveNegativeTwist
