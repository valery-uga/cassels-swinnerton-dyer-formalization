import PfaffianDescent.CorayPositiveFiniteCoproductCohomology

/-! SOURCE ONLY / UNVERIFIED146. Genuine native H1 vanishing for the
actual finite weighted positive free term. This is an independent input
for a future THREE-kernel ideal-H1/global-section construction. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME actual finite positive free term has H1=0, by the native
individual positive-twist vanishing and actual biproduct/coproduct comparison.
No supplied free-term, ideal-H1 or global-section-surjectivity premise. -/
theorem actualPositiveFiniteCoproduct_cohomology_one_subsingleton
    (K : Type u) [Field K]
    [hExt : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    {ι : Type u} [Fintype ι] (d : ι → ℕ) (m : ℕ) :
    Subsingleton (schemeModuleCohomology
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (∐ fun i => positiveSheafOfModules
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (m - d i)) 1) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let P := Proj PS
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExt
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  let M : ι → P.Modules := fun i => positiveSheafOfModules PS (m - d i)
  letI : ∀ i, Subsingleton (schemeModuleCohomology P (M i) 1) := fun i =>
    (p3_positiveTwist_cohomology_one_two_three_subsingleton (K := K) (m - d i)).1
  letI : HasFiniteBiproducts P.Modules := CategoryTheory.Abelian.hasFiniteBiproducts
  letI : Subsingleton (Ext.{u} O (⨁ M) 1) :=
    (Ext.addEquivBiproduct O (biproduct.isBilimit M) 1).injective.subsingleton
  exact ext_subsingleton_of_iso_right (biproduct.isoCoproduct M) 1

end PfaffianDescent.Coray
