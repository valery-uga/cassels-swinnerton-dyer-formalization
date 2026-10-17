import PfaffianDescent.FourTermResolutionCohomology
import PfaffianDescent.OriginalThreeQuadricInducedHZero
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.VoisinNegativeTwistGlobalH0

/-! SOURCE ONLY / UNVERIFIED. The literal TeX603–617 cohomological proof,
on the actual O(3)-twisted resolution and SAME induced augmentation.
The older independent graded-algebra bijection is NOT used in this proof. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)
-- SAME primitive geometric inputs are declaration-local.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Infrastructure-explicit version: the actual negative-twist providers
and finite target-biproduct Ext equivalence derive every required vanishing. -/
theorem p3OriginalThreeQuadricOThreeGlobalAugmentation_bijective_by_cohomology
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    [HasExt.{u} (Proj PS).Modules] :
    Function.Bijective
      (p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ) := by
  let X := Proj PS
  let A := sheafOfModules PS 3
  let B := ⨁ threeQuadricSheafTriple K 1
  -- Transfer the SAME given small-universe Ext instance to the raw sheaf category.
  let hExt : HasExt.{u} (Proj PS).Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  have hA := p3_negativeTwist_cohomology_one_and_two_subsingleton K 3
  have hOne := p3_negativeTwist_cohomology_one_and_two_subsingleton K 1
  letI : Subsingleton (schemeModuleCohomology X A 1) := hA.1
  letI : Subsingleton (schemeModuleCohomology X A 2) := hA.2
  letI : Subsingleton (sheafOfModules PS 1).sections :=
    p3_negativeTwist_sections_subsingleton_of_pos K 1 (by decide)
  letI : Subsingleton (schemeModuleCohomology X (sheafOfModules PS 1) 0) :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections X
      (sheafOfModules PS 1)).mpr inferInstance
  letI : Subsingleton (schemeModuleCohomology X (sheafOfModules PS 1) 1) := hOne.1
  letI : ∀ j : Fin 3,
      Subsingleton (schemeModuleCohomology X (threeQuadricSheafTriple K 1 j) 0) :=
    fun _ => inferInstance
  letI : ∀ j : Fin 3,
      Subsingleton (schemeModuleCohomology X (threeQuadricSheafTriple K 1 j) 1) :=
    fun _ => inferInstance
  letI : Subsingleton (schemeModuleCohomology X B 0) :=
    resolution_ext_finite_biproduct_target_subsingleton
      (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (threeQuadricSheafTriple K 1) 0
  letI : Subsingleton (schemeModuleCohomology X B 1) :=
    resolution_ext_finite_biproduct_target_subsingleton
      (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (threeQuadricSheafTriple K 1) 1
  have hres := p3OriginalThreeQuadricOThree_displayed_resolution f g h l hZ
  letI : Mono (threeQuadricOThreeKoszulFirst K f g h) := hres.1
  letI : Epi (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ) := hres.2.2.2
  change Function.Bijective (schemeModuleGlobalSectionsMap base
    (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ))
  exact resolution_fourTerm_globalMap_bijective base
    (threeQuadricOThreeKoszulFirst K f g h)
    (threeQuadricOThreeKoszulMiddle K f g h)
    (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ)
    (threeQuadricOThreeKoszul_first_middle_zero K f g h)
    (p3OriginalThreeQuadricOThree_middle_augmentation_zero f g h l hZ)
    hres.2.1 hres.2.2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Paper-facing version: HasExt and EnoughInjectives are internally derived
for the actual P3 module-sheaf category; no vanishing/exactness premise. -/
theorem p3OriginalThreeQuadricOThreeGlobalAugmentation_cohomological_bijective
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    Function.Bijective
      (p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ) := by
  letI : HasExt.{u} (Proj PS).Modules := resolutionSchemeModules_hasExt _
  exact p3OriginalThreeQuadricOThreeGlobalAugmentation_bijective_by_cohomology
    f g h l hZ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual H0(O(1)^3) ≃ H0(I_originalZ(3)), with the SAME forward map.
This is constructed using the cohomological bijection, not the graded one. -/
def p3OriginalThreeQuadricOThreeCohomologicalGlobalEquiv
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    SchemeModuleGlobalSectionsOver base (⨁ (p3ActualPositiveOneTriple (K := K))) ≃ₗ[K]
      SchemeModuleGlobalSectionsOver base
        (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))
          (positiveSheafOfModules PS 3)) :=
  LinearEquiv.ofBijective
    (p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ)
    (p3OriginalThreeQuadricOThreeGlobalAugmentation_cohomological_bijective f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The cohomological equivalence retains the existing actual induced-H0
polynomial formula. The forward map is definitionally the augmentation. -/
theorem p3OriginalThreeQuadricOThreeCohomologicalGlobalEquiv_polynomial
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    (s : SchemeModuleGlobalSectionsOver base (⨁ (p3ActualPositiveOneTriple (K := K)))) :
    (p3ClosedImmersionIdealHomogeneousKernelEquiv (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) 3
      (by decide) (p3OriginalThreeQuadricOThreeCohomologicalGlobalEquiv f g h l hZ s)).val =
      (threeQuadricCubicIdealLinearMap f g h
        (p3ActualPositiveOneTripleHomogeneousEquiv s)).val :=
  p3OriginalThreeQuadricOThreeGlobalAugmentation_polynomial f g h l hZ s

end PfaffianDescent
