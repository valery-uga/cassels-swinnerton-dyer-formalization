import AllCharacteristics.SchemeSpecialization
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Degree-one points and rational points

This file proves the degree-one case using actual scheme residue fields and
constructs a section over the base field. No assumption of algebraic closure
or separability is needed.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
universe u

/-- The spectrum of the residue field of a field-valued base is that base itself. -/
theorem isIso_fromSpecResidueField_of_field (k : Type u) [Field k]
    (x : Spec (.of k)) : IsIso ((Spec (.of k)).fromSpecResidueField x) := by
  have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  subst x
  let r := (Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k)
  let a := (Spec (.of k)).descResidueField (Scheme.stalkClosedPointTo (𝟙 (Spec (.of k))))
  have hs : Spec.map a ≫ r = 𝟙 _ := by
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k
      (Spec (.of k)) (𝟙 (Spec (.of k)))
  have : IsPreimmersion r :=
    Scheme.instIsPreimmersionFromSpecResidueField (X := Spec (.of k))
      (IsLocalRing.closedPoint k)
  have : Mono r := inferInstance
  have : IsSplitEpi r := IsSplitEpi.mk' ⟨Spec.map a, hs⟩
  exact isIso_of_mono_of_isSplitEpi r

/-- Residue degree one makes the residue-field homomorphism an isomorphism. -/
theorem isIso_residueFieldMap_of_degree_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (hx : f.residueDegree x = 1) : IsIso (f.residueFieldMap x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hd : Module.finrank (Y.residueField (f x)) (X.residueField x) = 1 := hx
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd

/-- A point of residue degree one on a scheme over a field gives a rational
point, expressed as a section of its structure morphism. -/
theorem section_of_residueDegree_one {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X) (hx : f.residueDegree x = 1) :
    ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  have := isIso_residueFieldMap_of_degree_one f x hx
  have := isIso_fromSpecResidueField_of_field k (f x)
  refine ⟨inv ((Spec (.of k)).fromSpecResidueField (f x)) ≫
    Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  simp only [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp,
    IsIso.inv_hom_id]

end AllCharacteristics
