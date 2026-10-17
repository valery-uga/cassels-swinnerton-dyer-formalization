import PfaffianDescent.CorayNativeFiniteCoproductExt

/-! Actual negative weighted finite coproduct cohomology over the original field.
The sole declaration body below is preserved verbatim from root137,
whose isolated actual-type and standard-axiom checks passed in 1216. -/
noncomputable section

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- ALL original negative weighted free terms have zero native H2 and
finite native H3. The actual negative twist residue producer derives each
summand's finiteness; the canonical native coproduct linear comparison
retains the independently original ambient base action. -/
theorem actualNegativeFiniteCoproduct_cohomology_two_zero_three_finite
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {ι : Type u} [Fintype ι] (d : ι → ℕ) :
    let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    letI : Linear K P.Modules :=
      schemeModulesLinearOver (AllCharacteristics.HomogeneousProjective.ambientToBase
        (R := K) (σ := Fin 4))
    Subsingleton (schemeModuleCohomology P
      (∐ fun i => sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)) 2) ∧
    Module.Finite K (schemeModuleCohomology P
      (∐ fun i => sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)) 3) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  letI : Linear K P.Modules := schemeModulesLinearOver
    (AllCharacteristics.HomogeneousProjective.ambientToBase (R := K) (σ := Fin 4))
  letI : HasFiniteBiproducts P.Modules := CategoryTheory.Abelian.hasFiniteBiproducts
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let M : ι → P.Modules := fun i => sheafOfModules PS (d i)
  letI : ∀ i, Subsingleton (Ext.{u} O (M i) 2) := fun i =>
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K (d i)).2
  letI : Subsingleton (Ext.{u} O (⨁ M) 2) :=
    (nativeExtBiproductLinearEquiv (K := K) O M 2).injective.subsingleton
  have hz : Subsingleton (Ext.{u} O (∐ M) 2) :=
    (nativeExtRightIsoLinearEquiv (K := K) O (biproduct.isoCoproduct M) 2).symm.injective.subsingleton
  letI : ∀ i, Module.Finite K (Ext.{u} O (M i) 3) := fun i =>
    p3NegativeTwist_cohomology_three_finite_over_ambient_base K (d i)
  exact ⟨hz, nativeExt_finiteCoproduct_target_finite O M 3⟩

end PfaffianDescent.Coray
