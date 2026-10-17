import PfaffianDescent.CorayPositiveFiniteCoproductHOne
import PfaffianDescent.CorayActualPositiveTwoTermKernelPresentation
import PfaffianDescent.CorayActualPositiveTwoTermQuasicoherentKernels
import PfaffianDescent.CorayActualPositiveThirdRelationPairExact
import PfaffianDescent.CorayNativeThreeKernelHOne
import PfaffianDescent.CorayFourAffineCoverCohomologicalDimension

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

/-- Three literal polynomial terms give H1 of the SAME whole ambient ideal
twist. The two original kernel sequences and third sequence are constructed
here from the genuine generator and two polynomial kernel span equalities. -/
theorem actualPositiveThreeTermPresentation_idealTwist_hOne_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules]
    (I : HomogeneousIdeal PS) {ι κ τ : Type u}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (g : ι → PolyA) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → PolyA) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (s : τ → κ → PolyA) (f : τ → ℕ)
    (hs : ∀ l, ActualWeightedPolynomialHomogeneous e (f l) (s l))
    (hspanG : Ideal.span (Set.range g) = I.toIdeal)
    (hspanR : Submodule.span PolyA (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hspanS : Submodule.span PolyA (Set.range s) = (actualPolynomialRelationMap r).ker)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) (hf : ∀ l, f l ≤ m) :
    Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m)) 1) := by
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  obtain ⟨a, ha, hz, htwo⟩ :=
    actualPositiveFinitePresentation_exists_twoKernelSequences
      I g d hg r e hr hspanG hspanR m hd he
  let R := actualPositiveFiniteRelationMap d r e hr m he
  let S := actualPositiveFiniteRelationMap e s f hs m hf
  let b := kernel.lift a R hz
  let T := actualPositiveFiniteRelationPairComplex
    g d r e hr s f hs hspanR hspanS m he hf
  have hT : T.Exact := actualPositiveFiniteRelationPairComplex_exact
    g d r e hr s f hs hspanR hspanS m he hf
  obtain ⟨hsb, hcEpi, hc, hthird⟩ :=
    nativeThirdKernelSequence_of_exactRelationPair a R hz S T.zero hT
  let c := kernel.lift b S hsb
  have hQC := actualPositiveFiniteRelationLift_kernels_isQuasicoherent I d r e hr m he a hz
  letI : (kernel b).IsQuasicoherent := hQC.2
  letI : (∐ fun l => positiveSheafOfModules PS (m - f l)).IsQuasicoherent :=
    actualPositiveFiniteCoproduct_isQuasicoherent f m
  letI : (kernel c).IsQuasicoherent := schemeNative_kernel_isQuasicoherent c
  letI : Subsingleton (schemeModuleCohomology P (kernel c) 4) :=
    p3_quasicoherent_cohomology_subsingleton_ge_four K (kernel c) 4 (by decide)
  letI : Subsingleton (schemeModuleCohomology P
      (∐ fun i => positiveSheafOfModules PS (m - d i)) 1) :=
    actualPositiveFiniteCoproduct_cohomology_one_subsingleton K d m
  letI : Subsingleton (schemeModuleCohomology P
      (∐ fun a => positiveSheafOfModules PS (m - e a)) 2) :=
    (actualPositiveFiniteCoproduct_cohomology_two_three_subsingleton K e m).1
  letI : Subsingleton (schemeModuleCohomology P
      (∐ fun l => positiveSheafOfModules PS (m - f l)) 3) :=
    (actualPositiveFiniteCoproduct_cohomology_two_three_subsingleton K f m).2
  exact nativeExt_threeKernelSequences_subsingleton
    (show P.Modules from SheafOfModules.unit P.ringCatSheaf)
    a R hz S hsb htwo.2.2.1 htwo.2.2.2 hthird

end PfaffianDescent.Coray
