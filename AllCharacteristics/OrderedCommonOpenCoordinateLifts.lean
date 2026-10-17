import AllCharacteristics.RelativeCommonOpenMembership
import AllCharacteristics.RelativeConfigurationOpen
import AllCharacteristics.RelativeConfigurationPermutations
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Lifting ordered coordinates into a common open chart

An ordered configuration whose coordinates stay in one open chart has
coordinate morphisms into that chart. This supplies the actual chart maps
from which regular coordinate sections can be pulled back.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- Every coordinate map of an ordered configuration confined to the image
of an open immersion lifts to that immersion's source. -/
theorem exists_orderedConfiguration_coordinate_lifts
    {X S U W : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (j : W ⟶ X) [IsOpenImmersion j]
    (i : U ⟶ (orderedFamilyConfigurationOver f 8).left)
    (hinside : ∀ u : U, (i u).val ∈
      orderedFamilyCommonOpen f j.opensRange 8) :
    ∀ k : Fin 8, ∃ t : U ⟶ W,
      t ≫ j =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι f 8)) ≫
          (orderedFamilyCoordinate f 8 k).left := by
  intro k
  let a : U ⟶ X :=
    (i ≫ Over.Hom.left (orderedFamilyConfigurationι f 8)) ≫
      (orderedFamilyCoordinate f 8 k).left
  have hrange : Set.range a ⊆ Set.range j := by
    rintro x ⟨u, rfl⟩
    have hu := (mem_orderedFamilyCommonOpen_iff f j.opensRange 8
      (i u).val).mp (hinside u) k
    change Over.Hom.left (orderedFamilyCoordinate f 8 k) (i u).val ∈
      j.opensRange at hu
    change a u ∈ Set.range j
    exact hu
  exact ⟨IsOpenImmersion.lift j a hrange,
    IsOpenImmersion.lift_fac j a hrange⟩

/-- A field-valued point of an open immersion's image lifts as a morphism
of schemes, since the spectrum of a field has only one point. -/
theorem exists_fieldPoint_lift_through_openImmersion
    {L : Type u} [Field L]
    {U X : Scheme.{u}}
    (i : U ⟶ X) [IsOpenImmersion i]
    (a : Spec (.of L) ⟶ X)
    (hpoint : a (IsLocalRing.closedPoint L) ∈ Set.range i) :
    ∃ aU : Spec (.of L) ⟶ U, aU ≫ i = a := by
  have hrange : Set.range a ⊆ Set.range i := by
    rintro x ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst y
    exact hpoint
  exact ⟨IsOpenImmersion.lift i a hrange,
    IsOpenImmersion.lift_fac i a hrange⟩

end AllCharacteristics
