import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The family over varying base schemes

For a fixed scheme morphism, form its pullback over each scheme over the base.
The resulting total spaces form a functor, and their projections to the
varying bases form a Cartesian natural transformation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The total space of a fixed family after each change of base. -/
noncomputable def relativeFamilyFunctor : Over S ⥤ Scheme.{u} :=
  Over.pullback f ⋙ Over.forget X

/-- The projections of the pulled-back families to their varying bases. -/
noncomputable def relativeFamilyProjection : relativeFamilyFunctor f ⟶ Over.forget S where
  app T := pullback.fst T.hom f
  naturality {T U} φ := by
    change (pullback.lift (pullback.fst T.hom f ≫ φ.left) (pullback.snd T.hom f) _) ≫
      pullback.fst U.hom f = pullback.fst T.hom f ≫ φ.left
    exact pullback.lift_fst _ _ _

/-- The map between total spaces preserves the projection to the original family. -/
theorem relativeFamilyFunctor_map_snd {T U : Over S} (φ : T ⟶ U) :
    (relativeFamilyFunctor f).map φ ≫ pullback.snd U.hom f = pullback.snd T.hom f :=
  pullback.lift_snd _ _ _

/-- The natural transformation to the varying bases is Cartesian. -/
theorem isPullback_relativeFamilyFunctor {T U : Over S} (φ : T ⟶ U) :
    IsPullback ((relativeFamilyFunctor f).map φ) ((relativeFamilyProjection f).app T)
      ((relativeFamilyProjection f).app U) φ.left := by
  apply IsPullback.of_right _ ((relativeFamilyProjection f).naturality φ)
    (IsPullback.of_hasPullback U.hom f).flip
  rw [relativeFamilyFunctor_map_snd]
  change IsPullback (pullback.snd T.hom f) (pullback.fst T.hom f) f (φ.left ≫ U.hom)
  rw [Over.w φ]
  exact (IsPullback.of_hasPullback T.hom f).flip

end AllCharacteristics
