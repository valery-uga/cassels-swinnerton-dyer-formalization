import PfaffianDescent.CorayOwnPositivePullbackCohomologyVanishing
import PfaffianDescent.CorayOwnPositiveH1CoordinateDescent

/-! Finite unit H1 of the SAME selected prime component over original perfect K.
Actual eventual positive-pullback H1 vanishing is constructed internally;
actual coordinate descent then returns to degree zero. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite original-K unit H1 of the actual selected component C. Its
positive vanishing, finite Cartier quotient sections, and backward descent
are all derived internally from the original equations and same C/P.
No finite-H1, vanishing, section-lifting, or comparison premise is supplied. -/
theorem perfectField_selectedProjectivePrimeComponent_unit_cohomology_one_finite_native
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : EnoughInjectives (scheme C).Modules :=
      sheafOfModules_enoughInjectives (scheme C).ringCatSheaf
    letI : HasExt.{u} (scheme C).Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme C).Modules
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    Module.Finite K (schemeModuleCohomology (scheme C)
      (SheafOfModules.unit (scheme C).ringCatSheaf) 1) := by
  letI : EnoughInjectives (scheme C).Modules :=
    sheafOfModules_enoughInjectives (scheme C).ringCatSheaf
  letI : HasExt.{u} (scheme C).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme C).Modules
  let A := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : EnoughInjectives A.Modules := sheafOfModules_enoughInjectives A.ringCatSheaf
  letI : HasExt.{u} A.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} A.Modules
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  exact selectedProjectivePrimeComponent_unitH1_finite_of_eventually_ownPositivePullback_vanishes
    p q hp hp0 n hq hnot C hIC hprime P
    (homogeneousIdeal_eventually_ownPositivePullback_cohomology_one_subsingleton C)

end PfaffianDescent.Coray
