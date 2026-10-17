import PfaffianDescent.FourTermResolutionCohomology
import PfaffianDescent.OriginalThreeQuadricOTwoResolution
import PfaffianDescent.ThreeQuadricOTwoScalarSections
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.VoisinNegativeTwistGlobalH0

/-! SOURCE ONLY / UNVERIFIED. The literal TeX603–617 cohomological proof,
on the actual O(2)-twisted resolution and SAME induced augmentation.
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
-- Primitive original geometry is bound separately at every declaration.

/-- The actual induced global map; no polynomial-space replacement. -/
def p3OriginalThreeQuadricOTwoGlobalAugmentationLinearMap
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    SchemeModuleGlobalSectionsOver base (⨁ p3OTwoActualUnitTriple K) →ₗ[K]
      SchemeModuleGlobalSectionsOver base
        (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
          (positiveSheafOfModules PS 2)) :=
  schemeModuleGlobalSectionsMap base
    (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Infrastructure-explicit version: the actual negative-twist providers
and finite target-biproduct Ext equivalence derive every required vanishing. -/
theorem p3OriginalThreeQuadricOTwoGlobalAugmentation_bijective_by_cohomology
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
      (p3OriginalThreeQuadricOTwoGlobalAugmentationLinearMap f g h l hZ) := by
  let X := Proj PS
  let A := sheafOfModules PS 4
  let B := ⨁ threeQuadricSheafTriple K 2
  -- Transfer the SAME given small-universe Ext instance to the raw sheaf category.
  let hExt : HasExt.{u} (Proj PS).Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  have hA := p3_negativeTwist_cohomology_one_and_two_subsingleton K 4
  have hOne := p3_negativeTwist_cohomology_one_and_two_subsingleton K 2
  letI : Subsingleton (schemeModuleCohomology X A 1) := hA.1
  letI : Subsingleton (schemeModuleCohomology X A 2) := hA.2
  letI : Subsingleton (sheafOfModules PS 2).sections :=
    p3_negativeTwist_sections_subsingleton_of_pos K 2 (by decide)
  letI : Subsingleton (schemeModuleCohomology X (sheafOfModules PS 2) 0) :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections X
      (sheafOfModules PS 2)).mpr inferInstance
  letI : Subsingleton (schemeModuleCohomology X (sheafOfModules PS 2) 1) := hOne.1
  letI : ∀ j : Fin 3,
      Subsingleton (schemeModuleCohomology X (threeQuadricSheafTriple K 2 j) 0) :=
    fun _ => inferInstance
  letI : ∀ j : Fin 3,
      Subsingleton (schemeModuleCohomology X (threeQuadricSheafTriple K 2 j) 1) :=
    fun _ => inferInstance
  letI : Subsingleton (schemeModuleCohomology X B 0) :=
    resolution_ext_finite_biproduct_target_subsingleton
      (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (threeQuadricSheafTriple K 2) 0
  letI : Subsingleton (schemeModuleCohomology X B 1) :=
    resolution_ext_finite_biproduct_target_subsingleton
      (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (threeQuadricSheafTriple K 2) 1
  have hres := p3OriginalThreeQuadricOTwo_displayed_resolution f g h l hZ
  letI : Mono (threeQuadricOTwoKoszulFirst K f g h) := hres.1
  letI : Epi (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ) := hres.2.2.2
  change Function.Bijective (schemeModuleGlobalSectionsMap base
    (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ))
  exact resolution_fourTerm_globalMap_bijective base
    (threeQuadricOTwoKoszulFirst K f g h)
    (threeQuadricOTwoKoszulMiddle K f g h)
    (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ)
    (threeQuadricOTwoKoszul_first_middle_zero K f g h)
    (p3OriginalThreeQuadricOTwo_middle_augmentation_zero f g h l hZ)
    hres.2.1 hres.2.2.1

/-- Paper-facing version: HasExt and EnoughInjectives are internally derived
for the actual P3 module-sheaf category; no vanishing/exactness premise. -/
theorem p3OriginalThreeQuadricOTwoGlobalAugmentation_cohomological_bijective
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    Function.Bijective
      (p3OriginalThreeQuadricOTwoGlobalAugmentationLinearMap f g h l hZ) := by
  letI : HasExt.{u} (Proj PS).Modules := resolutionSchemeModules_hasExt _
  exact p3OriginalThreeQuadricOTwoGlobalAugmentation_bijective_by_cohomology
    f g h l hZ

/-- Actual H0(O^3) ≃ H0(I_originalZ(2)), with the SAME forward map.
This is constructed using the cohomological bijection, not the graded one. -/
def p3OriginalThreeQuadricOTwoCohomologicalGlobalEquiv
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    SchemeModuleGlobalSectionsOver base (⨁ (p3OTwoActualUnitTriple K)) ≃ₗ[K]
      SchemeModuleGlobalSectionsOver base
        (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
          (positiveSheafOfModules PS 2)) :=
  LinearEquiv.ofBijective
    (p3OriginalThreeQuadricOTwoGlobalAugmentationLinearMap f g h l hZ)
    (p3OriginalThreeQuadricOTwoGlobalAugmentation_cohomological_bijective f g h l hZ)

/-- The actual scalar combination map K^3 → H0(I_originalZ(2)),
with its forward map definitionally induced by the SAME sheaf augmentation. -/
def p3OriginalThreeQuadricOTwoScalarAugmentationLinearMap
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    (Fin 3 → K) →ₗ[K] SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
        (positiveSheafOfModules PS 2)) :=
  (p3OriginalThreeQuadricOTwoGlobalAugmentationLinearMap f g h l hZ).comp
    (p3OTwoScalarTripleLinearMap K)

theorem p3OriginalThreeQuadricOTwoScalarAugmentation_bijective
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    Function.Bijective (p3OriginalThreeQuadricOTwoScalarAugmentationLinearMap f g h l hZ) :=
  (p3OriginalThreeQuadricOTwoGlobalAugmentation_cohomological_bijective f g h l hZ).comp
    (p3OTwoScalarTripleLinearMap_bijective K)

def p3OriginalThreeQuadricOTwoCohomologicalScalarEquiv
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    (Fin 3 → K) ≃ₗ[K] SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
        (positiveSheafOfModules PS 2)) :=
  (p3OTwoScalarTripleLinearEquiv K).trans
    (p3OriginalThreeQuadricOTwoCohomologicalGlobalEquiv f g h l hZ)

/-- Literal remark: H0(I_originalZ(2)) has dimension THREE, derived by
O(2)-tensoring the displayed resolution and the genuine sheaf LES.
The separate already accepted intrinsic/dictionary dimension proof is unused. -/
theorem p3OriginalThreeQuadricOTwoIdealHZero_finrank_by_cohomology
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
        f.val g.val h.val f.property g.property h.property)) = 8) :
    Module.finrank K (SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
        (positiveSheafOfModules PS 2))) = 3 := by
  rw [← (p3OriginalThreeQuadricOTwoCohomologicalScalarEquiv f g h l hZ).finrank_eq]
  simp only [Module.finrank_fin_fun]

end PfaffianDescent
