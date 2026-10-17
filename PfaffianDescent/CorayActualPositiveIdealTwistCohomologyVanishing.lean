import PfaffianDescent.CorayPositiveFiniteCoproductCohomology
import PfaffianDescent.CorayActualPositiveTwoTermKernelPresentation
import PfaffianDescent.CorayActualPositiveTwoTermQuasicoherentKernels
import PfaffianDescent.CorayFourAffineCoverCohomologicalDimension
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SheafModuleOverExtComparison

/-! Genuine eventual H2 of the OWN whole ideal and H1 of the actual twisted
quotient, from TWO actual weighted free terms and QC of the actual S2.
No desired vanishing, finite H1 or global lifting certificate is input.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem nativeExt_twoKernelSequences_subsingleton
    {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]
    (P : C) {F₀ F₁ J : C} (a : F₀ ⟶ J) (r : F₁ ⟶ F₀)
    (hz : r ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact)
    [Subsingleton (Ext.{u} P F₀ 2)] [Subsingleton (Ext.{u} P F₁ 3)]
    [Subsingleton (Ext.{u} P (kernel (kernel.lift a r hz)) 4)] :
    Subsingleton (Ext.{u} P J 2) := by
  let S₁ := ShortComplex.mk (kernel.ι (kernel.lift a r hz))
    (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))
  let S₀ := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  letI : Subsingleton (Ext.{u} P (kernel a) 3) :=
    ext_subsingleton_of_middle_and_next_left P S₁ h₁ 3
  exact ext_subsingleton_of_middle_and_next_left P S₀ h₀ 2

private theorem actualPositiveIdealTwist_H2_of_originalSequences
    [hExt : HasExt.{u} (Proj PS).Modules]
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → PolyA) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (he : ∀ a, e a ≤ m)
    (a : (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m))
    (hz : actualPositiveFiniteRelationMap d r e hr m he ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a
      (actualPositiveFiniteRelationMap d r e hr m he) hz))
      (kernel.lift a (actualPositiveFiniteRelationMap d r e hr m he) hz)
      (kernel.condition (kernel.lift a
        (actualPositiveFiniteRelationMap d r e hr m he) hz))).ShortExact) :
    Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 2) := by
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  let b := kernel.lift a (actualPositiveFiniteRelationMap d r e hr m he) hz
  have hQC := actualPositiveFiniteRelationLift_kernels_isQuasicoherent
    I d r e hr m he a hz
  letI : (kernel b).IsQuasicoherent := hQC.2
  letI : Subsingleton (schemeModuleCohomology P (kernel b) 4) :=
    p3_quasicoherent_cohomology_subsingleton_ge_four K (kernel b) 4 (by decide)
  letI : Subsingleton (schemeModuleCohomology P
      (∐ fun i => positiveSheafOfModules PS (m - d i)) 2) :=
    (actualPositiveFiniteCoproduct_cohomology_two_three_subsingleton K d m).1
  letI : Subsingleton (schemeModuleCohomology P
      (∐ fun a => positiveSheafOfModules PS (m - e a)) 3) :=
    (actualPositiveFiniteCoproduct_cohomology_two_three_subsingleton K e m).2
  exact nativeExt_twoKernelSequences_subsingleton
    (show P.Modules from SheafOfModules.unit P.ringCatSheaf)
    a (actualPositiveFiniteRelationMap d r e hr m he) hz h₀ h₁

/-- For EVERY actual whole homogeneous ideal, H2 of its OWN ideal twist
vanishes in all sufficiently large degrees. The bound and both weighted
terms are internally constructed; no chosen resolution/QC/Serre premise. -/
theorem homogeneousIdeal_eventually_actualIdealTwist_cohomology_two_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (Proj PS)
        (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
          (positiveSheafOfModules PS m)) 2) := by
  obtain ⟨T, d, R, e, B, hg, hr, hspanG, hspanR, hd, he, hpres⟩ :=
    homogeneousIdeal_exists_actualPositiveTwoKernelSequences I
  refine ⟨B, fun m hm => ?_⟩
  obtain ⟨a, ha, hz, htwo⟩ := hpres m
    (fun i => (hd i).trans hm) (fun a => (he a).trans hm)
  exact actualPositiveIdealTwist_H2_of_originalSequences I d
    (fun a : R => a.val) e hr m (fun a => (he a).trans hm)
    a hz htwo.2.2.1 htwo.2.2.2

/-- The SAME actual ideal tensor restriction sequence is short exact for a
positive twist, using the original standard-open unit frames. -/
private theorem actualPositiveIdealTwistSequence_shortExact
    (I : HomogeneousIdeal PS) (m : ℕ) (hm : 0 < m) :
    (closedImmersionIdealTwistSequence (quotientProjMap I)
      (positiveSheafOfModules PS m)).ShortExact := by
  apply closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    (quotientProjMap I) (p3StandardOpenLifted (K := K))
    (p3StandardOpenLifted_coversTop K)
  intro i
  exact overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) i.down)
    (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)

/-- Actual H1 of i_*O_C tensor O(m) vanishes eventually for the OWN literal
whole homogeneous ideal C. Its quotient remains the original tensor object;
no projection-formula identification is silently assumed. -/
theorem homogeneousIdeal_eventually_actualTwistedQuotient_cohomology_one_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (I : HomogeneousIdeal PS) :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (Proj PS)
        (closedImmersionIdealTwistSequence (quotientProjMap I)
          (positiveSheafOfModules PS m)).X₃ 1) := by
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  obtain ⟨B, hB⟩ := homogeneousIdeal_eventually_actualIdealTwist_cohomology_two_subsingleton I
  refine ⟨max B 1, fun m hm => ?_⟩
  have hmB : B ≤ m := (Nat.le_max_left B 1).trans hm
  have hmpos : 0 < m := (Nat.lt_add_one 0).trans_le
    ((Nat.le_max_right B 1).trans hm)
  let T := positiveSheafOfModules PS m
  let S := closedImmersionIdealTwistSequence (quotientProjMap I) T
  have hS : S.ShortExact := actualPositiveIdealTwistSequence_shortExact I m hmpos
  letI : Subsingleton (schemeModuleCohomology P S.X₁ 2) := hB m hmB
  letI : Subsingleton (schemeModuleCohomology P T 1) :=
    (p3_positiveTwist_cohomology_one_two_three_subsingleton (K := K) m).1
  letI : Subsingleton (schemeModuleCohomology P S.X₂ 1) :=
    schemeModuleCohomology_subsingleton_of_iso P (schemeModuleTensorUnitLeftIso T).symm 1
  exact schemeModuleCohomology_subsingleton_of_middle_and_next_left P S hS 1

end PfaffianDescent.Coray
