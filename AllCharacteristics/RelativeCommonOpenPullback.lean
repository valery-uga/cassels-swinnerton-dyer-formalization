import AllCharacteristics.RelativeCommonOpenInclusions

/-!
# Cartesian overlaps of the actual common-open tuple charts

The ordered power of an intersection of original opens is the actual
scheme-theoretic intersection of their ordered-power charts. The proof uses
the proved coordinate-membership criterion and injectivity of the open
chart immersions, not an assumed overlap model.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (U V : X.Opens) (n : ℕ)

/-- The tuple charts of two opens and their original intersection form an actual Cartesian square. -/
theorem isPullback_commonOpenPowerIntersection :
    IsPullback
      (Over.Hom.left (commonOpenPowerInclusion f (show U ⊓ V ≤ U from inf_le_left) n))
      (Over.Hom.left (commonOpenPowerInclusion f (show U ⊓ V ≤ V from inf_le_right) n))
      (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n))
      (Over.Hom.left (orderedFamilyCommonOpenPowerMap f V n)) := by
  let Z := (orderedFamilyPowerOver ((U ⊓ V).ι ≫ f) n).left
  let A := (orderedFamilyPowerOver (U.ι ≫ f) n).left
  let B := (orderedFamilyPowerOver (V.ι ≫ f) n).left
  let P := (orderedFamilyPowerOver f n).left
  let l : Z ⟶ A := Over.Hom.left (commonOpenPowerInclusion f (show U ⊓ V ≤ U from inf_le_left) n)
  let r : Z ⟶ B := Over.Hom.left (commonOpenPowerInclusion f (show U ⊓ V ≤ V from inf_le_right) n)
  let u : A ⟶ P := Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n)
  let v : B ⟶ P := Over.Hom.left (orderedFamilyCommonOpenPowerMap f V n)
  let k : Z ⟶ P := Over.Hom.left (orderedFamilyCommonOpenPowerMap f (U ⊓ V) n)
  have hl : l ≫ u = k := congrArg Over.Hom.left
    (commonOpenPowerInclusion_toPower f (show U ⊓ V ≤ U from inf_le_left) n)
  have hr : r ≫ v = k := congrArg Over.Hom.left
    (commonOpenPowerInclusion_toPower f (show U ⊓ V ≤ V from inf_le_right) n)
  change IsPullback l r u v
  apply IsOpenImmersion.isPullback
  · exact hr.trans hl.symm
  · apply le_antisymm
    · intro y hy
      have hyU : v y ∈ orderedFamilyCommonOpen f U n := hy
      have hyV : v y ∈ orderedFamilyCommonOpen f V n := ⟨y, rfl⟩
      have hyUV : v y ∈ orderedFamilyCommonOpen f (U ⊓ V) n := by
        rw [orderedFamilyCommonOpen_inf]
        exact ⟨hyU, hyV⟩
      obtain ⟨z, hz⟩ := hyUV
      refine ⟨z, v.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun m : Z ⟶ P ↦ m z) hr).trans hz
    · rintro _ ⟨z, rfl⟩
      have hz : k z ∈ orderedFamilyCommonOpen f (U ⊓ V) n := ⟨z, rfl⟩
      rw [orderedFamilyCommonOpen_inf] at hz
      change v (r z) ∈ orderedFamilyCommonOpen f U n
      have he : v (r z) = k z := congrArg (fun m : Z ⟶ P ↦ m z) hr
      rw [he]
      exact hz.1

end AllCharacteristics
