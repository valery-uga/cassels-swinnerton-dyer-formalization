import AllCharacteristics.ClosedPointFiniteSubscheme
import AllCharacteristics.DisjointFiniteSubschemeUnion

/-!
# Enlarging a closed point by disjoint finite subschemes

Coray's degree-ten alternative is represented by the residue-field closed
immersion of a closed point.  Adjoining two disjoint affine finite subschemes
to it gives an actual finite-flat embedded subscheme of the summed rank.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- A closed point and two subsequently disjoint affine finite subschemes
form one finite-subscheme datum, with rank the sum of their degrees. -/
noncomputable def finiteSubschemeDatumOfClosedPointAndTwoDisjointSpecSubschemes
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) (m : ℕ)
    (hx : f.residueDegree x.1 = m)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (n p : ℕ)
    (hni : (i ≫ f).finrank (IsLocalRing.closedPoint k) = n)
    (hpj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = p)
    (hxi : Disjoint (Set.range (X.fromSpecResidueField x.1)) (Set.range i))
    (hxij : Disjoint
      (Set.range (disjointSpecUnionMap (X.fromSpecResidueField x.1) i)) (Set.range j)) :
    FiniteSubschemeDatum f (m + n + p) := by
  let q : Spec (.of (X.residueField x.1)) ⟶ X := X.fromSpecResidueField x.1
  letI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  letI : Algebra k (X.residueField x.1) := pointAlgebra f x.1
  letI : Module.Finite k (X.residueField x.1) := closedPoint_moduleFinite f x
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap k (X.residueField x.1))) := by
    dsimp only [q]
    exact (pointAlgebra_spec f x.1).symm
  haveI : IsFinite (q ≫ f) := by
    rw [hq]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hmq : (q ≫ f).finrank (IsLocalRing.closedPoint k) = m := by
    calc
      (q ≫ f).finrank (IsLocalRing.closedPoint k) = finiteSchemeRank (q ≫ f) :=
        (finiteSchemeRank_eq_finrank (q ≫ f)).symm
      _ = f.residueDegree x.1 := by
        dsimp only [q]
        exact closedPoint_finiteSchemeRank_eq_residueDegree f x
      _ = m := hx
  have hxi' : Disjoint (Set.range q) (Set.range i) := by
    dsimp [q]
    exact hxi
  have hxij' : Disjoint (Set.range (disjointSpecUnionMap q i)) (Set.range j) := by
    dsimp [q]
    exact hxij
  exact finiteSubschemeDatumOfThreeDisjointSpecUnion f q i j hq hi hj m n p hmq hni hpj
    hxi' hxij'

/-- The numerical form used with Coray's degree-ten point and two
hyperplane-square components. -/
noncomputable def finiteSubschemeDatum_rankSixteenOfDegreeTenPointAndTwoRankThreeSubschemes
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X)
    (hx : f.residueDegree x.1 = 10)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hni : (i ≫ f).finrank (IsLocalRing.closedPoint k) = 3)
    (hpj : (j ≫ f).finrank (IsLocalRing.closedPoint k) = 3)
    (hxi : Disjoint (Set.range (X.fromSpecResidueField x.1)) (Set.range i))
    (hxij : Disjoint
      (Set.range (disjointSpecUnionMap (X.fromSpecResidueField x.1) i)) (Set.range j)) :
    FiniteSubschemeDatum f 16 := by
  simpa using finiteSubschemeDatumOfClosedPointAndTwoDisjointSpecSubschemes
    f x 10 hx i j hi hj 3 3 hni hpj hxi hxij

end AllCharacteristics
