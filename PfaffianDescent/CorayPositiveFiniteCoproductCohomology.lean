import PfaffianDescent.CorayPositiveNativeIntrinsicCohomologyVanishing
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Finite positive free-term vanishing in the actual SECOND Ext variable.
The actual coproduct is retained, via its canonical biproduct comparison.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem nativeExt_finiteCoproduct_target_subsingleton
    {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]
    {ι : Type*} [Fintype ι] (P : C) (M : ι → C) (n : ℕ)
    [∀ i, Subsingleton (Ext.{u} P (M i) n)] :
    Subsingleton (Ext.{u} P (∐ M) n) := by
  letI : HasFiniteBiproducts C := CategoryTheory.Abelian.hasFiniteBiproducts
  letI : Subsingleton (Ext.{u} P (⨁ M) n) :=
    (Ext.addEquivBiproduct P (biproduct.isBilimit M) n).injective.subsingleton
  exact ext_subsingleton_of_iso_right (biproduct.isoCoproduct M) n

/-- Actual H2/H3 vanish for every original finite weighted positive free
term. Each nonnegative positive twist vanishes by the accepted native P3
producer; the actual finite coproduct comparison supplies the whole term. -/
theorem actualPositiveFiniteCoproduct_cohomology_two_three_subsingleton
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {ι : Type u} [Fintype ι] (d : ι → ℕ) (m : ℕ) :
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (∐ fun i => positiveSheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (m - d i)) 2) ∧
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (∐ fun i => positiveSheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (m - d i)) 3) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let M : ι → P.Modules := fun i => positiveSheafOfModules PS (m - d i)
  letI : ∀ i, Subsingleton (schemeModuleCohomology P (M i) 2) := fun i =>
    (p3_positiveTwist_cohomology_one_two_three_subsingleton (K := K) (m - d i)).2.1
  letI : ∀ i, Subsingleton (schemeModuleCohomology P (M i) 3) := fun i =>
    (p3_positiveTwist_cohomology_one_two_three_subsingleton (K := K) (m - d i)).2.2
  exact ⟨nativeExt_finiteCoproduct_target_subsingleton O M 2,
    nativeExt_finiteCoproduct_target_subsingleton O M 3⟩

end PfaffianDescent.Coray
