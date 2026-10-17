import PfaffianDescent.CorayPerfectOwnUnitH1Finite
import PfaffianDescent.CorayPerfectOwnNormalizationH1LinearSurjection
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite intrinsic H1 of the SAME selected component's actual normalization
for original perfect K. Source H1 finiteness and the actual original-K
normalization surjection are constructed internally. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite original-K intrinsic unit H1 on the actual normalization of
same selected prime component C. Original pi and nu followed by pi scalar
actions, full C, and full native normalization are retained. No finite-H1,
vanishing, support, comparison or genus hypothesis is added. -/
theorem perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_cohomology_one_finite_native
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase C)
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase C)
    Module.Finite K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase C)
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase C)
  letI : LocallyOfFiniteType (toBase C) := inferInstance
  letI : Module.Finite K (schemeModuleCohomology X
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1) :=
    perfectField_selectedProjectivePrimeComponent_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot C hIC hprime P
  let g := perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase C)
  have hsurj : Function.Surjective g :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_intrinsicCohomologyOneLinearMap_surjective
      p q hp hp0 n hq hnot C hIC hprime P
  exact Module.Finite.of_surjective g hsurj

end PfaffianDescent.Coray
