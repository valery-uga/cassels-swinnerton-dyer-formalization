import PfaffianDescent.ThreeQuadricOTwoActualAugmentation
import PfaffianDescent.OriginalThreeQuadricOTwoCohomologicalHZero

/-! SOURCE ONLY / UNVERIFIED. SAME sheaf-induced scalar map, with literal
ambient formula c0*f+c1*g+c2*h. Bijectivity uses the genuine sheaf LES. -/
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
-- SAME finite triple, original closed embedding and rank are declaration-local.

/-- Three-term biproduct composition is checked in an abstract genuine
preadditive category, before any actual Proj module dictionaries. -/
private theorem oTwoScalarAugmentation_lift_desc_three
    {D : Type*} [Category D] [Preadditive D]
    (P : Fin 3 → D) [HasBiproduct P] {U V : D}
    (a : ∀ r, U ⟶ P r) (b : ∀ r, P r ⟶ V) :
    biproduct.lift a ≫ biproduct.desc b =
      a 0 ≫ b 0 + a 1 ≫ b 1 + a 2 ≫ b 2 := by
  simpa only [Fin.sum_univ_three] using
    (biproduct.lift_desc (g := a) (h := b))

/-- The actual scalar augmentation followed by the actual original ideal
inclusion gives precisely the homogeneous quadric sum. -/
theorem p3OriginalThreeQuadricOTwoScalarAugmentation_polynomial
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
        f.val g.val h.val f.property g.property h.property)) = 8) (c : Fin 3 → K) :
    p3OriginalThreeQuadricOTwoScalarAugmentationLinearMap f g h l hZ c ≫
      (closedImmersionIdealTwistSequence (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 2)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
    p3HomogeneousGlobalSectionLinearMap K 2 (c 0 • f + c 1 • g + c 2 • h) := by
  change p3OTwoScalarTripleLinearMap K c ≫
    p3OriginalThreeQuadricOTwoAugmentation f g h l hZ ≫
    (closedImmersionIdealTwistSequence (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 2)).f ≫
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom = _
  rw [p3OriginalThreeQuadricOTwoAugmentation_ambient_eq_sum]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  change _ =
    (schemeModuleConstantEndomorphism base (c 0) ≫
      p3HomogeneousGlobalSectionLinearMap K 2 f) +
    (schemeModuleConstantEndomorphism base (c 1) ≫
      p3HomogeneousGlobalSectionLinearMap K 2 g) +
    (schemeModuleConstantEndomorphism base (c 2) ≫
      p3HomogeneousGlobalSectionLinearMap K 2 h)
  dsimp only [p3OTwoScalarTripleLinearMap, p3OTwoUnitScalarLinearMap]
  exact oTwoScalarAugmentation_lift_desc_three (p3OTwoActualUnitTriple K)
    (fun r => schemeModuleConstantEndomorphism base (c r))
    ![p3HomogeneousGlobalSectionLinearMap K 2 f,
      p3HomogeneousGlobalSectionLinearMap K 2 g,
      p3HomogeneousGlobalSectionLinearMap K 2 h]

/-- The cohomological scalar equivalence has exactly the SAME actual
scalar augmentation as its forward map. -/
theorem p3OriginalThreeQuadricOTwoCohomologicalScalarEquiv_forward
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
    (p3OriginalThreeQuadricOTwoCohomologicalScalarEquiv f g h l hZ).toLinearMap =
      p3OriginalThreeQuadricOTwoScalarAugmentationLinearMap f g h l hZ := rfl

end PfaffianDescent
