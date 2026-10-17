import PfaffianDescent.CorayNegativeTwoKernelFiniteCohomology
import PfaffianDescent.CorayNativeShortExactPairFiniteCohomology
import PfaffianDescent.ActualWeightedFreeCoproductUntwistIso
import PfaffianDescent.NativeRankOneTensorQuasicoherent

/-! SOURCE ONLY / UNVERIFIED. Actual untwist H2 integration, split from all
pairing constructions and positive-presentation producers. Original actions. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem actualWeightedUntwistedFreeCoproduct_cohomology_three_finite
    [hExt : HasExt.{u} (Proj PS).Modules]
    {ι : Type u} [Fintype ι] (B : ℕ) (d : ι → ℕ) (hd : ∀ i, d i ≤ B) :
    letI : Linear K (Proj PS).Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (∐ fun i => positiveSheafOfModules PS (B - d i)) (sheafOfModules PS B)) 3) := by
  let P := Proj PS
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let M : P.Modules := ∐ fun i => sheafOfModules PS (d i)
  let W : P.Modules := schemeModuleTensor
    (∐ fun i => positiveSheafOfModules PS (B - d i)) (sheafOfModules PS B)
  let c : W ≅ M := p3WeightedFreeCoproductUntwistIso K B d hd
  letI : Module.Finite K (schemeModuleCohomology P M 3) :=
    (actualNegativeFiniteCoproduct_cohomology_two_zero_three_finite K d).2
  exact Module.Finite.equiv (nativeExtRightIsoLinearEquiv O c 3).symm

private theorem actualWeightedUntwistedFreeCoproduct_cohomology_two_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules]
    {ι : Type u} [Fintype ι] (B : ℕ) (d : ι → ℕ) (hd : ∀ i, d i ≤ B) :
    Subsingleton (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (∐ fun i => positiveSheafOfModules PS (B - d i)) (sheafOfModules PS B)) 2) := by
  let P := Proj PS
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let M : P.Modules := ∐ fun i => sheafOfModules PS (d i)
  let W : P.Modules := schemeModuleTensor
    (∐ fun i => positiveSheafOfModules PS (B - d i)) (sheafOfModules PS B)
  let c : W ≅ M := p3WeightedFreeCoproductUntwistIso K B d hd
  letI : Subsingleton (schemeModuleCohomology P M 2) :=
    (actualNegativeFiniteCoproduct_cohomology_two_zero_three_finite K d).1
  exact (nativeExtRightIsoLinearEquiv (K := K) O c 2).injective.subsingleton

private theorem actualNegativeTensor_cohomology_four_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (B : ℕ) (M : (Proj PS).Modules)
    [M.IsQuasicoherent] :
    Subsingleton (schemeModuleCohomology (Proj PS) (schemeModuleTensor M (sheafOfModules PS B)) 4) := by
  letI : (schemeModuleTensor M (sheafOfModules PS B)).IsQuasicoherent :=
    p3ActualNegativeTensor_isQuasicoherent K B M
  exact p3_quasicoherent_cohomology_subsingleton_ge_four K
    (schemeModuleTensor M (sheafOfModules PS B)) 4 (by decide)

private theorem actualTwistUntwist_cohomology_two_finite
    [hExt : HasExt.{u} (Proj PS).Modules] (B : ℕ) (J : (Proj PS).Modules) :
    letI : Linear K (Proj PS).Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS)
      (schemeModuleTensor (schemeModuleTensor J (positiveSheafOfModules PS B)) (sheafOfModules PS B)) 2) →
      Module.Finite K (schemeModuleCohomology (Proj PS) J 2) := by
  let P := Proj PS
  letI : Linear K P.Modules := schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  intro hfinite
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let E := p3TwistTensorRightEquivalence K B
  let c : E.functor.obj (E.inverse.obj J) ≅ J := E.counitIso.app J
  letI : Module.Finite K (schemeModuleCohomology P (E.functor.obj (E.inverse.obj J)) 2) := hfinite
  exact Module.Finite.equiv (nativeExtRightIsoLinearEquiv O c 2)

/-- Untwist an ACTUAL positive two-kernel presentation to derive finite
zero-twist H2. All degree-zero cohomological input is derived from native
negative free terms and QC H4=0. The maps and kernel are retained literally. -/
theorem actualPositiveTwoKernelPresentation_untwist_cohomology_two_finite
    [hExt : HasExt.{u} (Proj PS).Modules]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (B : ℕ) (d : ι → ℕ) (e : κ → ℕ)
    (hd : ∀ i, d i ≤ B) (he : ∀ j, e j ≤ B)
    (J : (Proj PS).Modules)
    (a : (∐ fun i => positiveSheafOfModules PS (B - d i)) ⟶
      schemeModuleTensor J (positiveSheafOfModules PS B))
    (r : (∐ fun j => positiveSheafOfModules PS (B - e j)) ⟶
      (∐ fun i => positiveSheafOfModules PS (B - d i)))
    (hz : r ≫ a = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact)
    [(kernel (kernel.lift a r hz)).IsQuasicoherent] :
    letI : Linear K (Proj PS).Modules := schemeModulesLinearOver
      (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS) J 2) := by
  let P := Proj PS
  let pi := ambientToBase (R := K) (σ := Fin 4)
  letI : Linear K P.Modules := schemeModulesLinearOver pi
  let F : P.Modules ⥤ P.Modules := schemeModuleTensorRight (sheafOfModules PS B)
  let E := p3TwistTensorRightEquivalence K B
  letI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits E.functor
    infer_instance
  letI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits E.functor
    infer_instance
  let b := kernel.lift a r hz
  let S₁ : ShortComplex P.Modules := ShortComplex.mk (kernel.ι b) b (kernel.condition b)
  let S₀ : ShortComplex P.Modules := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  have hS₁ : S₁.ShortExact := h₁
  have hS₀ : S₀.ShortExact := h₀
  have hT₁ : (S₁.map F).ShortExact := hS₁.map_of_exact F
  have hT₀ : (S₀.map F).ShortExact := hS₀.map_of_exact F
  have hfinite : Module.Finite K (schemeModuleCohomology P (F.obj S₀.X₃) 2) :=
    nativeShortExactPair_right_cohomology_two_finite pi (S₀.map F) (S₁.map F) hT₀ hT₁ rfl
      (actualNegativeTensor_cohomology_four_subsingleton B (kernel b))
      (actualWeightedUntwistedFreeCoproduct_cohomology_three_finite B e he)
      (actualWeightedUntwistedFreeCoproduct_cohomology_two_subsingleton B d hd)
  exact actualTwistUntwist_cohomology_two_finite B J hfinite

end PfaffianDescent.Coray
