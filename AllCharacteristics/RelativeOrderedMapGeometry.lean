import AllCharacteristics.RelativeOrderedMaps
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Geometry of ordered-power morphisms and common-open charts

Coordinatewise open immersions induce open immersions of actual ordered
powers. Powers of affine schemes over an affine base are affine. In
particular, a common affine open in the original family supplies an actual
affine open chart of the ordered relative power.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Taking finite ordered powers preserves open immersions of families. -/
instance isOpenImmersion_orderedFamilyMap (a : Over.mk f ⟶ Over.mk g)
    [IsOpenImmersion (Over.Hom.left a)] (n : ℕ) :
    IsOpenImmersion (Over.Hom.left (orderedFamilyMap f g a n)) := by
  induction n with
  | zero =>
    change IsOpenImmersion (𝟙 S)
    infer_instance
  | succ n ih =>
    have := ih
    rw [orderedFamilyMap_succ_left]
    exact @Scheme.pullback_map_isOpenImmersion X (orderedFamilyPowerOver f n).left S
      Y (orderedFamilyPowerOver g n).left S f (orderedFamilyPowerOver f n).hom
      g (orderedFamilyPowerOver g n).hom (Over.Hom.left a)
      (Over.Hom.left (orderedFamilyMap f g a n)) (𝟙 S)
      ((Category.comp_id f).trans a.w.symm)
      ((Category.comp_id _).trans (orderedFamilyMap f g a n).w.symm)
      inferInstance ih inferInstance

/-- Every ordered fiber power of an affine scheme over an affine base is affine. -/
instance isAffine_orderedFamilyPower [IsAffine X] [IsAffine S] (n : ℕ) :
    IsAffine (orderedFamilyPowerOver f n).left := by
  induction n with
  | zero =>
    change IsAffine S
    infer_instance
  | succ n ih =>
    have := ih
    change IsAffine (pullback f (orderedFamilyPowerOver f n).hom)
    infer_instance

/-- The actual inclusion of tuples whose entries lie in a common open of the original family. -/
noncomputable def orderedFamilyCommonOpenPowerMap (U : X.Opens) (n : ℕ) :
    orderedFamilyPowerOver (U.ι ≫ f) n ⟶ orderedFamilyPowerOver f n :=
  orderedFamilyMap (U.ι ≫ f) f (Over.homMk U.ι rfl) n

/-- The common-open tuple map is an actual open immersion. -/
instance isOpenImmersion_orderedFamilyCommonOpenPowerMap (U : X.Opens) (n : ℕ) :
    IsOpenImmersion (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n)) := by
  change IsOpenImmersion (Over.Hom.left
    (orderedFamilyMap (U.ι ≫ f) f (Over.homMk U.ι rfl) n))
  have : IsOpenImmersion (Over.Hom.left
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ f) ⟶ Over.mk f)) := by
    change IsOpenImmersion U.ι
    infer_instance
  exact isOpenImmersion_orderedFamilyMap (U.ι ≫ f) f (Over.homMk U.ι rfl) n

/-- The common-open tuples define an actual open of the ordered relative power. -/
noncomputable def orderedFamilyCommonOpen (U : X.Opens) (n : ℕ) :
    (orderedFamilyPowerOver f n).left.Opens :=
  (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n)).opensRange

end AllCharacteristics
