import PfaffianDescent.CorayActualPositiveGlobalIdealImagePresentation
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The two native kernel sequences needed for the OWN ideal H2 route.
The finite weighted generators are the SAME original relation map.
No exactness, epi, QC-kernel or H1/Serre premise is supplied.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem kernelSequence_shortExact
    {C : Type*} [Category C] [Abelian C] {M N : C} (a : M ⟶ N) [Epi a] :
    (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact :=
  { exact := ShortComplex.exact_kernel a }

private theorem twoKernelSequences_of_exactEpi
    {C : Type*} [Category C] [Abelian C]
    {L M J : C} (r : L ⟶ M) (a : M ⟶ J) [Epi a]
    (hz : r ≫ a = 0) (h : (ShortComplex.mk r a hz).Exact) :
    let b := kernel.lift a r hz
    Epi b ∧ b ≫ kernel.ι a = r ∧
      (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact ∧
      (ShortComplex.mk (kernel.ι b) b (kernel.condition b)).ShortExact := by
  dsimp only
  let b := kernel.lift a r hz
  letI : Epi b := h.epi_kernelLift
  exact ⟨inferInstance, kernel.lift_ι a r hz,
    kernelSequence_shortExact a, kernelSequence_shortExact b⟩

/-- The SAME ideal factor internally gives two genuine short exact
sequences, with S1=kernel a and S2=kernel b. Its finite weighted generators
onto S1 are exactly the original relation map, as the displayed equality
b followed by kernel.ι a = R certifies. No new replacement relation map or
supplied desired kernel equality, epi or Serre conclusion. -/
theorem actualPositiveFinitePresentation_exists_twoKernelSequences
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → PolyA) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → PolyA) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hspanG : Ideal.span (Set.range g) = I.toIdeal)
    (hspanR : Submodule.span PolyA (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) :
    ∃ a : (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m),
      a ≫ actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m) =
        actualPositiveFiniteGeneratorMap g d hg m hd ∧
      ∃ hz : actualPositiveFiniteRelationMap d r e hr m he ≫ a = 0,
        let b := kernel.lift a (actualPositiveFiniteRelationMap d r e hr m he) hz
        Epi b ∧ b ≫ kernel.ι a = actualPositiveFiniteRelationMap d r e hr m he ∧
          (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact ∧
          (ShortComplex.mk (kernel.ι b) b (kernel.condition b)).ShortExact := by
  obtain ⟨a, hEpi, ha, hz, hExact⟩ :=
    actualPositiveFinitePresentation_exists_exact_epiIdealFactor
      I g d hg r e hr hspanG hspanR m hd he
  letI : Epi a := hEpi
  have htwo := twoKernelSequences_of_exactEpi
    (actualPositiveFiniteRelationMap d r e hr m he) a hz hExact
  exact ⟨a, ha, hz, htwo⟩

/-- The actual whole homogeneous ideal internally supplies finite weighted
terms and both native kernel short exact sequences in all sufficiently
large degrees. The original polynomial generators and relations are
constructed by the upstream whole-ideal producer, not supplied as a
finite-presentation, exactness or Serre hypothesis. -/
theorem homogeneousIdeal_exists_actualPositiveTwoKernelSequences
    (I : HomogeneousIdeal PS) :
    ∃ (T : Finset PolyA) (d : T → ℕ) (R : Finset (T → PolyA)) (e : R → ℕ) (B : ℕ)
      (hg : ∀ i : T, (i : PolyA).IsHomogeneous (d i))
      (hr : ∀ a : R, ActualWeightedPolynomialHomogeneous d (e a) a.val),
      Ideal.span (T : Set PolyA) = I.toIdeal ∧
      Submodule.span PolyA (R : Set (T → PolyA)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      (∀ i : T, d i ≤ B) ∧ (∀ a : R, e a ≤ B) ∧
      ∀ (m : ℕ) (hd : ∀ i : T, d i ≤ m) (he : ∀ a : R, e a ≤ m),
        ∃ a : (∐ fun i : T => positiveSheafOfModules PS (m - d i)) ⟶
          schemeModuleTensor (closedImmersionModule (quotientProjMap I))
            (positiveSheafOfModules PS m),
          a ≫ actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m) =
            actualPositiveFiniteGeneratorMap (fun i : T => i.val) d hg m hd ∧
          ∃ hz : actualPositiveFiniteRelationMap d (fun a : R => a.val) e hr m he ≫ a = 0,
            let b := kernel.lift a
              (actualPositiveFiniteRelationMap d (fun a : R => a.val) e hr m he) hz
            Epi b ∧
              b ≫ kernel.ι a = actualPositiveFiniteRelationMap d (fun a : R => a.val) e hr m he ∧
              (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact ∧
              (ShortComplex.mk (kernel.ι b) b (kernel.condition b)).ShortExact := by
  obtain ⟨T, d, R, e, B, hg, hr, hspanG, hspanR, hd, he, hpres⟩ :=
    homogeneousIdeal_exists_actualPositiveExactEpiIdealPresentation I
  refine ⟨T, d, R, e, B, hg, hr, hspanG, hspanR, hd, he, ?_⟩
  intro m hdm hem
  obtain ⟨a, hEpi, ha, hz, hExact⟩ := hpres m hdm hem
  letI : Epi a := hEpi
  have htwo := twoKernelSequences_of_exactEpi
    (actualPositiveFiniteRelationMap d (fun a : R => a.val) e hr m hem) a hz hExact
  exact ⟨a, ha, hz, htwo⟩

end PfaffianDescent.Coray
