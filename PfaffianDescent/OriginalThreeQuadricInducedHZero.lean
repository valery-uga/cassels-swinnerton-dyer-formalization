import PfaffianDescent.ThreeQuadricOThreeSignedMatrix
import PfaffianDescent.OriginalThreeQuadricOThreeResolution
import PfaffianDescent.ActualP3HomogeneousQuadricGlobalMultiplication
import PfaffianDescent.ActualP3IdealHomogeneousKernelEmbedding

/-! SOURCE ONLY / UNVERIFIED. The genuine induced H0 map of the SAME
native O(3)-twisted augmentation is exactly the literal cubic sum H1*f +
H2*g + H3*h, and exactly the genuine original ideal-global equivalence.
No desired map equality, H0 equivalence or coordinate certificate is an input. -/
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
local notation "T3" => schemeModuleTensorRight (positiveSheafOfModules PS 3)
-- Primitive finite-triple and original closed rank-eight inputs are declaration-local.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original ideal augmentation, under its actual ambient
inclusion, is the literal row of positive quadric multiplications. -/
theorem p3OriginalThreeQuadricOThreeAugmentation_ambient_eq_sum
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
    p3OriginalThreeQuadricOThreeAugmentation f g h l hZ ≫
      (closedImmersionIdealTwistSequence (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 3)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
    biproduct.desc ![positiveMulHomogeneous PS f 1,
      positiveMulHomogeneous PS g 1, positiveMulHomogeneous PS h 1] := by
  change ((p3OThreeTensorNegativeTwoTripleIso K).inv ≫
    (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) ≫
    (T3).map (IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))) ≫
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom = _
  calc
    _ = (p3OThreeTensorNegativeTwoTripleIso K).inv ≫
      (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ ≫
        IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property))) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom := by
        simp only [Functor.map_comp, Category.assoc]
    _ = (p3OThreeTensorNegativeTwoTripleIso K).inv ≫
      (T3).map (threeQuadricSheafKoszulLast K f g h) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom := by
        rw [p3OriginalThreeQuadricSheafAugmentation_comp]
    _ = _ := threeQuadricOThreeKoszulLast_ambient_eq_sum K f g h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual induced linear H0 map of the native twisted augmentation. -/
def p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap
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
    SchemeModuleGlobalSectionsOver base (⨁ (p3ActualPositiveOneTriple (K := K))) →ₗ[K]
      SchemeModuleGlobalSectionsOver base
        (closedImmersionIdealTwist (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 3)) :=
  schemeModuleGlobalSectionsMap base
    (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact literal polynomial formula for the INDUCED actual H0 map. -/
theorem p3OriginalThreeQuadricOThreeGlobalAugmentation_polynomial
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
      f.val g.val h.val f.property g.property h.property)) 3 (by decide)
      (p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ s)).val =
      (threeQuadricCubicIdealLinearMap f g h
        (p3ActualPositiveOneTripleHomogeneousEquiv s)).val := by
  apply p3HomogeneousGlobalSectionLinearMap_injective K 3 (by decide)
  rw [p3ClosedImmersionIdealHomogeneousKernelEquiv_embedding]
  change (s ≫ p3OriginalThreeQuadricOThreeAugmentation f g h l hZ) ≫
    (closedImmersionIdealTwistSequence (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 3)).f ≫
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom = _
  simp only [Category.assoc]
  rw [p3OriginalThreeQuadricOThreeAugmentation_ambient_eq_sum]
  exact p3ActualThreeQuadricPositiveSum_global f g h s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual induced H0 map is the previously proved genuine original
H0 isomorphism, with exactly the same embedding and coefficient sum. -/
theorem p3OriginalThreeQuadricOThreeGlobalAugmentation_eq_cubicGlobalEquiv
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
    p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ =
      (p3OriginalThreeQuadricCubicGlobalEquiv f g h l hZ).toLinearMap := by
  apply LinearMap.ext
  intro s
  apply (p3ClosedImmersionIdealHomogeneousKernelEquiv (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
      (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)) 3 (by decide)).injective
  apply Subtype.ext
  exact (p3OriginalThreeQuadricOThreeGlobalAugmentation_polynomial f g h l hZ s).trans
    (p3OriginalThreeQuadricCubicGlobalEquiv_polynomial f g h l hZ s).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Bijectivity of the actual induced H0 map, derived internally from the
same finite triple/original length-eight data. -/
theorem p3OriginalThreeQuadricOThreeGlobalAugmentation_bijective
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
    Function.Bijective (p3OriginalThreeQuadricOThreeGlobalAugmentationLinearMap f g h l hZ) := by
  rw [p3OriginalThreeQuadricOThreeGlobalAugmentation_eq_cubicGlobalEquiv]
  exact (p3OriginalThreeQuadricCubicGlobalEquiv f g h l hZ).bijective

end PfaffianDescent
