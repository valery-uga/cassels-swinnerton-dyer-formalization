import AllCharacteristics.ClosedPointRank

/-!
# Closed points as finite extensions of the base field

The base algebra on a point's residue field is induced by its actual morphism
to the base. At a closed point of a scheme locally of finite type over a field,
it is finite and its vector-space dimension is the full residue degree.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
namespace AllCharacteristics
universe u

/-- The algebra on a point's residue field induced by an arbitrary affine
base morphism. Unlike `pointAlgebra`, the base need not be a field. -/
noncomputable abbrev pointAlgebraOf
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X) :
    Algebra R (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra

/-- The algebra induced by an arbitrary affine base morphism recovers that
morphism after passing to the residue field. -/
theorem pointAlgebraOf_spec
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X) :
    letI := pointAlgebraOf f x
    Spec.map (CommRingCat.ofHom (algebraMap R (X.residueField x))) =
      X.fromSpecResidueField x ≫ f := by
  exact Spec.map_preimage (X.fromSpecResidueField x ≫ f)

/-- The base-field algebra on the residue field of an actual scheme point. -/
noncomputable abbrev pointAlgebra
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra

/-- The algebra structure reproduces the given point-to-base morphism. -/
theorem pointAlgebra_spec
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI := pointAlgebra f x
    Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x))) =
      X.fromSpecResidueField x ≫ f := by
  exact Spec.map_preimage (X.fromSpecResidueField x ≫ f)

/-- Closed points give finite extensions of the base field. -/
theorem closedPoint_moduleFinite
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    letI := pointAlgebra f x.1
    Module.Finite k (X.residueField x.1) := by
  let a := Spec.preimage (X.fromSpecResidueField x.1 ≫ f)
  have : IsFinite (Spec.map a) := by
    dsimp only [a]
    rw [Spec.map_preimage]
    infer_instance
  exact (IsFinite.SpecMap_iff a).mp inferInstance

/-- The vector-space dimension of a closed point's residue field is its
scheme-theoretic residue degree, without any separability hypothesis. -/
theorem closedPoint_finrank_eq_residueDegree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    letI := pointAlgebra f x.1
    Module.finrank k (X.residueField x.1) = f.residueDegree x.1 := by
  let := pointAlgebra f x.1
  have := closedPoint_moduleFinite f x
  let g := X.fromSpecResidueField x.1 ≫ f
  have hg : Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x.1))) = g :=
    pointAlgebra_spec f x.1
  have hr : g.finrank (IsLocalRing.closedPoint k) =
      Module.finrank k (X.residueField x.1) := by
    rw [← hg, Scheme.Hom.finrank_SpecMap_algebraMap]
    exact congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := X.residueField x.1)) _
  exact hr.symm.trans ((finiteSchemeRank_eq_finrank g).symm.trans
    (closedPoint_finiteSchemeRank_eq_residueDegree f x))

/-- The degree of an actual effective cycle is the weighted sum of the
vector-space dimensions of its support residue fields over the base field. -/
theorem EffectiveZeroCycle.degree_eq_sum_finrank
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (z : EffectiveZeroCycle X) :
    EffectiveZeroCycle.degree f z =
      ∑ x : z.support, z x.1 * (letI := pointAlgebra f x.1.1
        Module.finrank k (X.residueField x.1.1)) := by
  classical
  calc
    EffectiveZeroCycle.degree f z =
        ∑ x : z.support, z x.1 * f.residueDegree x.1.1 :=
      (Finset.sum_coe_sort z.support (fun x ↦ z x * f.residueDegree x.1)).symm
    _ = _ := Finset.sum_congr rfl (fun x _ ↦
      congrArg (z x.1 * ·) (closedPoint_finrank_eq_residueDegree f x.1).symm)

end AllCharacteristics
