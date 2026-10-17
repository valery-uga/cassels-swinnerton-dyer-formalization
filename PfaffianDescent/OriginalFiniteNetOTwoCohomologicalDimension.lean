import PfaffianDescent.OriginalThreeQuadricOTwoCohomologicalHZero

/-! SOURCE ONLY / UNVERIFIED. The O(2)-LES method applied to SAME original
ambient closed Z, with its actual net containment. Its factor into the
finite intersection and source finiteness are derived, not hypotheses. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)
-- Primitive original geometry is bound separately at every declaration.

private theorem oTwoFiniteRank_eq_of_map_eq {X : Scheme.{u}}
    (a b : X ⟶ Spec (.of K)) [IsFinite a] [IsFinite b] (hab : a = b) :
    AllCharacteristics.finiteSchemeRank a = AllCharacteristics.finiteSchemeRank b := by
  subst b
  rfl

/-- Transport actual ideal-twist H0 together with its closed-immersion instance. -/
private theorem oTwoIdealHZero_finrank_eq_of_map_eq {Z : Scheme.{u}}
    (a b : Z ⟶ Proj PS) [IsClosedImmersion a] [IsClosedImmersion b] (hab : a = b) :
    Module.finrank K (SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist a (positiveSheafOfModules PS 2))) =
    Module.finrank K (SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist b (positiveSheafOfModules PS 2))) := by
  subst b
  rfl

/-- The SAME original closed immersion factors uniquely through its net. -/
def p3OTwoOriginalFiniteNetLift
    (f g h : PS 2)
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker) : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property) :=
  IsClosedImmersion.lift (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) i hker

@[reassoc]
theorem p3OTwoOriginalFiniteNetLift_ambient
    (f g h : PS 2)
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker) :
    p3OTwoOriginalFiniteNetLift f g h i hker ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property) = i :=
  IsClosedImmersion.lift_fac (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) i hker

instance p3OTwoOriginalFiniteNetLift_isClosedImmersion
    (f g h : PS 2)
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker) :
    IsClosedImmersion (p3OTwoOriginalFiniteNetLift f g h i hker) := by
  letI : IsClosedImmersion
      (p3OTwoOriginalFiniteNetLift f g h i hker ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) := by
    rw [p3OTwoOriginalFiniteNetLift_ambient]
    infer_instance
  exact IsClosedImmersion.of_comp
    (p3OTwoOriginalFiniteNetLift f g h i hker) (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))

theorem p3OTwoOriginalFiniteNetLift_base
    (f g h : PS 2)
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker) :
    p3OTwoOriginalFiniteNetLift f g h i hker ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property) = i ≫ base := by
  rw [← quotientProjMap_toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property), ← Category.assoc,
    p3OTwoOriginalFiniteNetLift_ambient]

theorem p3OTwoOriginalFiniteNet_source_isFinite
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker) : IsFinite (i ≫ base) := by
  rw [← p3OTwoOriginalFiniteNetLift_base f g h i hker]
  infer_instance

/-- Literal original-Z H0 dimension THREE by O(2)-tensoring and LES.
Structural input: actual finite net through closed Z of length8. No
ambient/global comparison, resolution, vanishing, regularity or dimension
certificate; no infinite/perfect-field restriction, no Chapter3 theorem. -/
theorem p3OriginalFiniteNet_idealHZero_finrank_by_OTwo_cohomology
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (hker : (quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker ≤ i.ker)
    (hZ : letI : IsFinite (i ≫ base) :=
        p3OTwoOriginalFiniteNet_source_isFinite f g h i hker
      AllCharacteristics.finiteSchemeRank (i ≫ base) = 8) :
    Module.finrank K (SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist i (positiveSheafOfModules PS 2))) = 3 := by
  letI : IsFinite (i ≫ base) :=
    p3OTwoOriginalFiniteNet_source_isFinite f g h i hker
  let l := p3OTwoOriginalFiniteNetLift f g h i hker
  have hZ' : AllCharacteristics.finiteSchemeRank (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8 := by
    exact (oTwoFiniteRank_eq_of_map_eq _ _
      (p3OTwoOriginalFiniteNetLift_base f g h i hker)).trans hZ
  have hd := p3OriginalThreeQuadricOTwoIdealHZero_finrank_by_cohomology f g h l hZ'
  exact (oTwoIdealHZero_finrank_eq_of_map_eq _ _
    (p3OTwoOriginalFiniteNetLift_ambient f g h i hker)).symm.trans hd

end PfaffianDescent
