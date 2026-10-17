import AllCharacteristics.CycleDegrees
import AllCharacteristics.SchemeDegreeComparison
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Effective cycles supplied by a closed subscheme

Closed immersions preserve residue fields and therefore the degrees of the
closed points and of their effective zero-cycles.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u

/-- Surjectivity on stalks makes the induced residue-field maps isomorphisms. -/
theorem isIso_residueFieldMap_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (i : X ⟶ Y) [SurjectiveOnStalks i] (x : X) :
    IsIso (i.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(i.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) z
  obtain ⟨b, rfl⟩ := i.stalkMap_surjective x a
  refine ⟨Y.residue (i x) b, ?_⟩
  exact congr($(Scheme.residue_residueFieldMap i x) b)

/-- Precomposing with a map which preserves the residue field preserves the
residue degree to an ambient base. -/
theorem residueDegree_comp_of_residueFieldMap_isIso
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    [IsIso (i.residueFieldMap x)] : (i ≫ f).residueDegree x = f.residueDegree (i x) := by
  let a := (f.residueFieldMap (i x)).hom
  let b := (i.residueFieldMap x).hom
  let := a.toAlgebra
  let := (b.comp a).toAlgebra
  let e := (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv
  have h : Module.finrank (Z.residueField (f (i x))) (X.residueField x) =
      Module.finrank (Z.residueField (f (i x))) (Y.residueField (i x)) := by
    apply (Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.refl (Z.residueField (f (i x)))) e ?_).symm
    rfl
  unfold Scheme.Hom.residueDegree
  rw [Scheme.residueFieldMap_comp]
  exact h

/-- A closed immersion sends closed points to closed points. -/
def closedPointMap {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] :
    closedPoints X → closedPoints Y := fun x ↦
  ⟨i x.1, by
    change IsClosed {i x.1}
    rw [← Set.image_singleton]
    exact i.isClosedMap _ x.2⟩

/-- An effective cycle on a closed subscheme, regarded as a cycle on the ambient
scheme. The residue-field factors equal one for a closed immersion. -/
noncomputable def pushforwardClosedCycle {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] (z : EffectiveZeroCycle X) : EffectiveZeroCycle Y :=
  z.mapDomain (closedPointMap i)

/-- The closed-immersion pushforward preserves the total degree to a base. -/
theorem degree_pushforwardClosedCycle
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Z)
    (z : EffectiveZeroCycle X) :
    EffectiveZeroCycle.degree f (pushforwardClosedCycle i z) =
      EffectiveZeroCycle.degree (i ≫ f) z := by
  let w : closedPoints Y → ℕ := fun x ↦ f.residueDegree x.1
  have hsum : (z.mapDomain (closedPointMap i)).sum (fun x n ↦ n * w x) =
      z.sum (fun x n ↦ n * w (closedPointMap i x)) :=
    Finsupp.sum_mapDomain_index
      (fun x : closedPoints Y ↦ Nat.zero_mul (w x))
      (fun (x : closedPoints Y) (n m : ℕ) ↦ Nat.add_mul n m (w x))
  refine hsum.trans ?_
  apply Finsupp.sum_congr
  intro x _
  have : IsIso (i.residueFieldMap x.1) := isIso_residueFieldMap_of_surjectiveOnStalks i x.1
  exact congrArg (fun d ↦ z x * d) (residueDegree_comp_of_residueFieldMap_isIso i f x.1).symm

end AllCharacteristics
