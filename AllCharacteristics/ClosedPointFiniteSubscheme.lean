import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.FiniteSubschemeFromImmersion

/-!
# Closed points as finite flat embedded subschemes

A closed point of a finite-type family over a field is represented by the
spectrum of its residue field.  This file packages that actual closed
immersion as an ideal-defined finite flat subscheme, with its full residue
degree as the constant rank.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics

universe u

/-- The residue-field embedding of a closed point is an actual finite flat
subscheme of its ambient finite-type family, of rank its full residue degree. -/
noncomputable def finiteSubschemeDatumOfClosedPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    FiniteSubschemeDatum f (f.residueDegree x.1) := by
  let q : Spec (.of (X.residueField x.1)) ⟶ X := X.fromSpecResidueField x.1
  letI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  letI : IsFinite (q ≫ f) := by
    dsimp only [q]
    infer_instance
  letI : Algebra k (X.residueField x.1) := pointAlgebra f x.1
  letI : Module.Finite k (X.residueField x.1) := closedPoint_moduleFinite f x
  haveI : Flat (q ≫ f) := by
    rw [← pointAlgebra_spec f x.1]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Module.FinitePresentation k (X.residueField x.1) :=
    Module.finitePresentation_of_finite k (X.residueField x.1)
  haveI : Algebra.FinitePresentation k (X.residueField x.1) :=
    Algebra.FinitePresentation.of_finitePresentation k (X.residueField x.1)
  haveI : LocallyOfFinitePresentation (q ≫ f) := by
    rw [← pointAlgebra_spec f x.1]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact finiteSubschemeDatumOfClosedImmersion q f (f.residueDegree x.1) (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst s
    exact (finiteSchemeRank_eq_finrank (q ≫ f)).symm.trans
      (closedPoint_finiteSchemeRank_eq_residueDegree f x))

/-- A stated residue-degree equality reindexes the closed-point subscheme to
that numerical rank. -/
noncomputable def finiteSubschemeDatumOfClosedPointOfResidueDegree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) (n : ℕ)
    (hx : f.residueDegree x.1 = n) : FiniteSubschemeDatum f n := by
  simpa only [hx] using finiteSubschemeDatumOfClosedPoint f x

/-- The ideal behind `finiteSubschemeDatumOfClosedPoint` is precisely the
kernel ideal of the residue-field closed immersion. -/
theorem finiteSubschemeDatumOfClosedPoint_ideal
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    (finiteSubschemeDatumOfClosedPoint f x).val =
      (X.fromSpecResidueField x.1).ker := by
  rw [finiteSubschemeDatumOfClosedPoint]
  rfl

end AllCharacteristics
