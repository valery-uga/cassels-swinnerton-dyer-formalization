import AllCharacteristics.RegularLocalSpecialization
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Rational sections specialize at regular points

This is the scheme corollary of the regular-local lemma in Section 3 of the
addendum. The rational section is an actual Mathlib rational map. Its domain is
not required to contain the point where specialization is performed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- A generic-fiber section of a universally closed morphism has a
residue-field-valued specialization at every regular point of its integral
base.  Only existence, rather than uniqueness, of the specialization is used. -/
theorem specialize_generic_section_at_regular_point
    {B X : Scheme.{u}} [IsIntegral B] (f : X ⟶ B) [UniversallyClosed f]
    (s : Spec B.functionField ⟶ X)
    (hs : s ≫ f = B.fromSpecStalk (genericPoint B))
    (b : B) [hreg : IsRegularLocalRing (B.presheaf.stalk b)] :
    ∃ q : Spec (B.residueField b) ⟶ X, q ≫ f = B.fromSpecResidueField b := by
  let a := CommRingCat.ofHom (algebraMap (B.presheaf.stalk b) B.functionField)
  have hcompat : s ≫ f = Spec.map a ≫ B.fromSpecStalk b := by
    rw [hs]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec B).specializes trivial)).symm
  let fb := pullback.snd f (B.fromSpecStalk b)
  have hg : HasPointOver fb (algebraMap (B.presheaf.stalk b) B.functionField) := by
    refine ⟨pullback.lift s (Spec.map a) hcompat, ?_⟩
    exact pullback.lift_snd _ _ _
  obtain ⟨q, hq⟩ := @specialize_proper_point_regularLocal
    (B.presheaf.stalk b) B.functionField _ hreg _ _ _ _ fb _ hg
  have hcomp : (q ≫ pullback.fst f (B.fromSpecStalk b)) ≫ f =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (B.presheaf.stalk b))) ≫
        B.fromSpecStalk b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
  exact ⟨q ≫ pullback.fst f (B.fromSpecStalk b), hcomp⟩

/-- An actual rational section specializes at every regular point, including
points outside the domain of definition of the rational map. -/
theorem specialize_rational_section_at_regular_point
    {B X : Scheme.{u}} [IsIntegral B] (f : X ⟶ B) [UniversallyClosed f]
    [LocallyOfFiniteType f]
    (s : B.RationalMap X) (hs : s.compHom f = Scheme.Hom.toRationalMap (𝟙 B))
    (b : B) [IsRegularLocalRing (B.presheaf.stalk b)] :
    ∃ q : Spec (B.residueField b) ⟶ X, q ≫ f = B.fromSpecResidueField b := by
  obtain ⟨q, hq⟩ := (Scheme.RationalMap.equivFunctionField (𝟙 B) f).symm ⟨s, hs⟩
  apply specialize_generic_section_at_regular_point f q _ b
  simpa only [Category.comp_id] using hq

/-- The universal-parameter-space form: a field-valued point of the regular
locus lifts through a universally closed finite-type morphism carrying a
rational section. -/
theorem lift_field_point_of_rational_section
    {B X : Scheme.{u}} [IsIntegral B] (f : X ⟶ B) [UniversallyClosed f]
    [LocallyOfFiniteType f]
    (s : B.RationalMap X) (hs : s.compHom f = Scheme.Hom.toRationalMap (𝟙 B))
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ B)
    [IsRegularLocalRing (B.presheaf.stalk (b (IsLocalRing.closedPoint k)))] :
    ∃ q : Spec (.of k) ⟶ X, q ≫ f = b := by
  obtain ⟨q, hq⟩ := specialize_rational_section_at_regular_point f s hs
    (b (IsLocalRing.closedPoint k))
  let e := B.descResidueField (Scheme.stalkClosedPointTo b)
  refine ⟨Spec.map e ≫ q, ?_⟩
  rw [Category.assoc, hq]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k B b

end AllCharacteristics
