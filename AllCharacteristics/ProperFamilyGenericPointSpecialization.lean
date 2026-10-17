import AllCharacteristics.RationalSectionSpecialization

/-!
# Specializing a point constructed over a parameter-space function field

Voisin's argument moves a finite subscheme to the generic point of a smooth
parameter space, performs the residual construction there, and specializes
the result back at the original field-valued parameter.  The valuative step
only needs the target family to be universally closed and locally of finite
type.  This file records that precise scheme-theoretic bridge and retains the
proper-family form as a convenient corollary.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- Let `X` be universally closed and locally of finite type over a field,
and let `B` be an integral parameter scheme with a regular `K`-point.  A
point of `X` over the function field of `B`, compatible with the structure
maps, specializes to a `K`-point of `X`.

The proof applies regular-local specialization to the constant family
`X × B → B`; no Chow-group specialization is used. -/
theorem universallyClosed_point_of_parameter_functionField_point
    {K : Type u} [Field K]
    {B X : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Spec (.of K))
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [LocallyOfFiniteType p]
    (c : Spec (.of K) ⟶ B) (hc : c ≫ b = 𝟙 _)
    [IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))]
    (s : Spec B.functionField ⟶ X)
    (hs : s ≫ p = B.fromSpecStalk (genericPoint B) ≫ b) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ p = 𝟙 _ := by
  let family : Scheme.{u} := pullback p b
  let familyToBase : family ⟶ B := pullback.snd p b
  let sg : Spec B.functionField ⟶ family :=
    pullback.lift s (B.fromSpecStalk (genericPoint B)) hs
  have hsg : sg ≫ familyToBase = B.fromSpecStalk (genericPoint B) := by
    exact pullback.lift_snd _ _ _
  let sr := (Scheme.RationalMap.equivFunctionField (𝟙 B) familyToBase)
    ⟨sg, by simpa only [Category.comp_id] using hsg⟩
  obtain ⟨q, hq⟩ := lift_field_point_of_rational_section
    familyToBase sr.val sr.property c
  refine ⟨q ≫ pullback.fst p b, ?_⟩
  calc
    (q ≫ pullback.fst p b) ≫ p = q ≫ (pullback.fst p b ≫ p) :=
      Category.assoc _ _ _
    _ = q ≫ (pullback.snd p b ≫ b) :=
      congrArg (q ≫ ·) pullback.condition
    _ = (q ≫ pullback.snd p b) ≫ b := (Category.assoc _ _ _).symm
    _ = c ≫ b := congrArg (· ≫ b) hq
    _ = 𝟙 _ := hc

/-- The proper-family form of generic-point specialization. -/
theorem proper_point_of_parameter_functionField_point
    {K : Type u} [Field K]
    {B X : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Spec (.of K))
    (p : X ⟶ Spec (.of K)) [IsProper p]
    (c : Spec (.of K) ⟶ B) (hc : c ≫ b = 𝟙 _)
    [IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))]
    (s : Spec B.functionField ⟶ X)
    (hs : s ≫ p = B.fromSpecStalk (genericPoint B) ≫ b) :
    ∃ q : Spec (.of K) ⟶ X, q ≫ p = 𝟙 _ :=
  universallyClosed_point_of_parameter_functionField_point b p c hc s hs

end AllCharacteristics
