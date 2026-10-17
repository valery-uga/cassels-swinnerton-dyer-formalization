import PfaffianDescent.P3TwistCanonicalDifference
import PfaffianDescent.PointGlobalTraceP3CoordinateKoszul
import PfaffianDescent.VoisinP3TopCechExtComparison
import PfaffianDescent.VoisinNegativeTwistGlobalH0

/-! # The six actual twist Ext vanishings for the ambient point resolution

The inverse-twist equivalence and actual degree-subtraction pairings reduce
these native projective Ext groups to already proved cohomology vanishings.
No Ext-vanishing or coordinate-compatibility hypothesis is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The native Ext from O(-1) to O(-4) is cohomology of O(-3). -/
def p3CanonicalTwistExtCohomologyEquiv_1
    [hExt : HasExt.{u} (Proj PS).Modules] (n : ℕ) :
    Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 1) (sheafOfModules PS 4) n ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 3) n := by
  letI : EnoughInjectives (Proj PS).Modules :=
    sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  let E := (p3TwistTensorRightEquivalence K 1).symm
  letI : E.functor.Additive := schemeModuleTensorRight_additive (positiveSheafOfModules PS 1)
  letI : IsIso (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl)) :=
    p3PositiveNegativeDifferencePairing_1_four_isIso K
  let eX : E.functor.obj (sheafOfModules PS 1) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
    p3NegativePositiveTensorInverseIso K 1
  let eY : E.functor.obj (sheafOfModules PS 4) ≅ sheafOfModules PS 3 :=
    schemeModuleTensorSymmetry _ _ ≪≫
      asIso (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))
  exact extAddEquivOfExactEquivalenceOfIsos.{u, u, u, u, u + 1, u + 1} (C := (Proj PS).Modules)
    (D := (Proj PS).Modules) E _ _ _ _ eX eY n

/-- The native Ext from O(-2) to O(-4) is cohomology of O(-2). -/
def p3CanonicalTwistExtCohomologyEquiv_2
    [hExt : HasExt.{u} (Proj PS).Modules] (n : ℕ) :
    Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 2) (sheafOfModules PS 4) n ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 2) n := by
  letI : EnoughInjectives (Proj PS).Modules :=
    sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  let E := (p3TwistTensorRightEquivalence K 2).symm
  letI : E.functor.Additive := schemeModuleTensorRight_additive (positiveSheafOfModules PS 2)
  letI : IsIso (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl)) :=
    p3PositiveNegativeDifferencePairing_2_four_isIso K
  let eX : E.functor.obj (sheafOfModules PS 2) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
    p3NegativePositiveTensorInverseIso K 2
  let eY : E.functor.obj (sheafOfModules PS 4) ≅ sheafOfModules PS 2 :=
    schemeModuleTensorSymmetry _ _ ≪≫
      asIso (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))
  exact extAddEquivOfExactEquivalenceOfIsos.{u, u, u, u, u + 1, u + 1} (C := (Proj PS).Modules)
    (D := (Proj PS).Modules) E _ _ _ _ eX eY n

/-- The native Ext from O(-3) to O(-4) is cohomology of O(-1). -/
def p3CanonicalTwistExtCohomologyEquiv_3
    [hExt : HasExt.{u} (Proj PS).Modules] (n : ℕ) :
    Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 3) (sheafOfModules PS 4) n ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 1) n := by
  letI : EnoughInjectives (Proj PS).Modules :=
    sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  let E := (p3TwistTensorRightEquivalence K 3).symm
  letI : E.functor.Additive := schemeModuleTensorRight_additive (positiveSheafOfModules PS 3)
  letI : IsIso (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl)) :=
    p3PositiveNegativeDifferencePairing_3_four_isIso K
  let eX : E.functor.obj (sheafOfModules PS 3) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf :=
    p3NegativePositiveTensorInverseIso K 3
  let eY : E.functor.obj (sheafOfModules PS 4) ≅ sheafOfModules PS 1 :=
    schemeModuleTensorSymmetry _ _ ≪≫
      asIso (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))
  exact extAddEquivOfExactEquivalenceOfIsos.{u, u, u, u, u + 1, u + 1} (C := (Proj PS).Modules)
    (D := (Proj PS).Modules) E _ _ _ _ eX eY n

theorem p3CanonicalTwistExt_1_2_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 1) (sheafOfModules PS 4) 2) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 3) 2) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).2
  exact (p3CanonicalTwistExtCohomologyEquiv_1 K 2).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTwistExt_1_3_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 1) (sheafOfModules PS 4) 3) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 3) 3) :=
    p3NegativeThree_cohomology_three_subsingleton K
  exact (p3CanonicalTwistExtCohomologyEquiv_1 K 3).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTwistExt_2_1_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 2) (sheafOfModules PS 4) 1) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 2) 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 2).1
  exact (p3CanonicalTwistExtCohomologyEquiv_2 K 1).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTwistExt_2_2_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 2) (sheafOfModules PS 4) 2) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 2) 2) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 2).2
  exact (p3CanonicalTwistExtCohomologyEquiv_2 K 2).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTwistExt_3_0_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 3) (sheafOfModules PS 4) 0) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 1) 0) :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections
      (Proj PS) (sheafOfModules PS 1)).mpr
      (p3_negativeTwist_sections_subsingleton_of_pos K 1 (of_decide_eq_true rfl))
  exact (p3CanonicalTwistExtCohomologyEquiv_3 K 0).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTwistExt_3_1_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 3) (sheafOfModules PS 4) 1) := by
  have h : Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 1) 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 1).1
  exact (p3CanonicalTwistExtCohomologyEquiv_3 K 1).toEquiv.subsingleton_congr.mpr h

theorem p3CanonicalTripleTwistExt_1_2_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 1)
      (sheafOfModules PS 4) 2) := by
  letI : ∀ j : Fin 3, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules) (pointGlobalTraceP3CoordinateTriple K 1 j) (sheafOfModules PS 4) 2) :=
    fun _ => p3CanonicalTwistExt_1_2_subsingleton K
  exact (Ext.biproductAddEquiv
    (biproduct.isBilimit (pointGlobalTraceP3CoordinateTriple K 1))
    (sheafOfModules PS 4) 2).toEquiv.subsingleton_congr.mpr inferInstance

theorem p3CanonicalTripleTwistExt_1_3_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 1)
      (sheafOfModules PS 4) 3) := by
  letI : ∀ j : Fin 3, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules) (pointGlobalTraceP3CoordinateTriple K 1 j) (sheafOfModules PS 4) 3) :=
    fun _ => p3CanonicalTwistExt_1_3_subsingleton K
  exact (Ext.biproductAddEquiv
    (biproduct.isBilimit (pointGlobalTraceP3CoordinateTriple K 1))
    (sheafOfModules PS 4) 3).toEquiv.subsingleton_congr.mpr inferInstance

theorem p3CanonicalTripleTwistExt_2_1_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 2)
      (sheafOfModules PS 4) 1) := by
  letI : ∀ j : Fin 3, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules) (pointGlobalTraceP3CoordinateTriple K 2 j) (sheafOfModules PS 4) 1) :=
    fun _ => p3CanonicalTwistExt_2_1_subsingleton K
  exact (Ext.biproductAddEquiv
    (biproduct.isBilimit (pointGlobalTraceP3CoordinateTriple K 2))
    (sheafOfModules PS 4) 1).toEquiv.subsingleton_congr.mpr inferInstance

theorem p3CanonicalTripleTwistExt_2_2_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 2)
      (sheafOfModules PS 4) 2) := by
  letI : ∀ j : Fin 3, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules) (pointGlobalTraceP3CoordinateTriple K 2 j) (sheafOfModules PS 4) 2) :=
    fun _ => p3CanonicalTwistExt_2_2_subsingleton K
  exact (Ext.biproductAddEquiv
    (biproduct.isBilimit (pointGlobalTraceP3CoordinateTriple K 2))
    (sheafOfModules PS 4) 2).toEquiv.subsingleton_congr.mpr inferInstance

/-- All six native vanishings, in the order required by the actual ambient
three-step point resolution. -/
theorem pointGlobalTraceAmbientTwistExt_six_vanishings
    [hExt : HasExt.{u} (Proj PS).Modules] :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 1)
      (sheafOfModules PS 4) 2) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 1)
      (sheafOfModules PS 4) 3) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 2)
      (sheafOfModules PS 4) 1) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (⨁ pointGlobalTraceP3CoordinateTriple K 2)
      (sheafOfModules PS 4) 2) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 3) (sheafOfModules PS 4) 0) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sheafOfModules PS 3) (sheafOfModules PS 4) 1) :=
  ⟨p3CanonicalTripleTwistExt_1_2_subsingleton K,
   p3CanonicalTripleTwistExt_1_3_subsingleton K,
   p3CanonicalTripleTwistExt_2_1_subsingleton K,
   p3CanonicalTripleTwistExt_2_2_subsingleton K,
   p3CanonicalTwistExt_3_0_subsingleton K,
   p3CanonicalTwistExt_3_1_subsingleton K⟩

end PfaffianDescent.ProjectiveNegativeTwist
