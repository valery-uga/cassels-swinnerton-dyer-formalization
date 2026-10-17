import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # The actual family map induced by a change of base

The map between the original pullback families is itself a Cartesian base
change of the base morphism. The projection identities and the finite,
étale, and surjective properties are retained explicitly.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S T U : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S) (b : U ⟶ S)
variable (t : T ⟶ U) (ht : t ≫ b = a)

/-- The actual morphism between the original pullback families induced by a base map. -/
noncomputable def baseChangedFamilyMap : pullback f a ⟶ pullback f b :=
  pullback.map f a f b (𝟙 X) t (𝟙 S) (by simp) (by simp [ht])

/-- The induced family map preserves the original projection to the family. -/
lemma baseChangedFamilyMap_fst :
    baseChangedFamilyMap f a b t ht ≫ pullback.fst f b = pullback.fst f a := by
  change pullback.map f a f b (𝟙 X) t (𝟙 S) (by simp) (by simp [ht]) ≫ pullback.fst f b = _
  rw [pullback.lift_fst, Category.comp_id]

/-- The induced family map has exactly the prescribed map on the bases. -/
lemma baseChangedFamilyMap_snd :
    baseChangedFamilyMap f a b t ht ≫ pullback.snd f b = pullback.snd f a ≫ t :=
  pullback.lift_snd _ _ _

/-- The induced family map is the actual Cartesian base change of the base map. -/
lemma isPullback_baseChangedFamilyMap :
    IsPullback (baseChangedFamilyMap f a b t ht) (pullback.snd f a) (pullback.snd f b) t := by
  apply IsPullback.of_right _ (baseChangedFamilyMap_snd f a b t ht)
    (IsPullback.of_hasPullback f b)
  rw [baseChangedFamilyMap_fst, ht]
  exact IsPullback.of_hasPullback f a

/-- A finite map of bases induces a finite map of the pullback families. -/
instance isFinite_baseChangedFamilyMap [IsFinite t] :
    IsFinite (baseChangedFamilyMap f a b t ht) :=
  MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_baseChangedFamilyMap f a b t ht).flip inferInstance

/-- An étale map of bases induces an étale map of the pullback families. -/
instance etale_baseChangedFamilyMap [Etale t] :
    Etale (baseChangedFamilyMap f a b t ht) :=
  MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_baseChangedFamilyMap f a b t ht).flip inferInstance

/-- A surjective map of bases induces a surjective map of the pullback families. -/
instance surjective_baseChangedFamilyMap [Surjective t] :
    Surjective (baseChangedFamilyMap f a b t ht) :=
  MorphismProperty.of_isPullback (P := @Surjective.{u})
    (isPullback_baseChangedFamilyMap f a b t ht).flip inferInstance

end AllCharacteristics
