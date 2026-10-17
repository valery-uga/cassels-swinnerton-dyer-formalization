import AllCharacteristics.RelativeCommonOpenIntersections

/-!
# Actual inclusions between common-open tuple charts

Inclusions of opens in the original family induce open immersions of its
ordered tuple charts. These morphisms agree with the original embeddings
into the full ordered power and respect identity and composition.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Inclusion between two actual open subfamilies over the same base. -/
noncomputable def commonOpenFamilyInclusion {U V : X.Opens} (h : U ≤ V) :
    Over.mk (U.ι ≫ f) ⟶ Over.mk (V.ι ≫ f) :=
  Over.homMk (X.homOfLE h) (by
    change X.homOfLE h ≫ (V.ι ≫ f) = U.ι ≫ f
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The family inclusion is an actual open immersion on underlying schemes. -/
instance isOpenImmersion_commonOpenFamilyInclusion {U V : X.Opens} (h : U ≤ V) :
    IsOpenImmersion (Over.Hom.left (commonOpenFamilyInclusion f h)) := by
  change IsOpenImmersion (X.homOfLE h)
  infer_instance

/-- The identity inclusion of open families is the actual identity morphism. -/
theorem commonOpenFamilyInclusion_id (U : X.Opens) :
    commonOpenFamilyInclusion f (le_refl U) = 𝟙 (Over.mk (U.ι ≫ f)) := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_rfl X U

/-- Inclusions of actual open families compose as their order relations. -/
theorem commonOpenFamilyInclusion_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    commonOpenFamilyInclusion f hUV ≫ commonOpenFamilyInclusion f hVW =
      commonOpenFamilyInclusion f (hUV.trans hVW) := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_homOfLE X hUV hVW

/-- The actual tuple-chart inclusion induced by an inclusion of original opens. -/
noncomputable def commonOpenPowerInclusion {U V : X.Opens} (h : U ≤ V) (n : ℕ) :
    orderedFamilyPowerOver (U.ι ≫ f) n ⟶ orderedFamilyPowerOver (V.ι ≫ f) n :=
  orderedFamilyMap (U.ι ≫ f) (V.ι ≫ f) (commonOpenFamilyInclusion f h) n

/-- The tuple-chart inclusion is an actual open immersion. -/
instance isOpenImmersion_commonOpenPowerInclusion {U V : X.Opens} (h : U ≤ V) (n : ℕ) :
    IsOpenImmersion (Over.Hom.left (commonOpenPowerInclusion f h n)) := by
  exact isOpenImmersion_orderedFamilyMap (U.ι ≫ f) (V.ι ≫ f) (commonOpenFamilyInclusion f h) n

/-- Inclusion of tuple charts commutes with their actual maps to the full ordered power. -/
theorem commonOpenPowerInclusion_toPower {U V : X.Opens} (h : U ≤ V) (n : ℕ) :
    commonOpenPowerInclusion f h n ≫ orderedFamilyCommonOpenPowerMap f V n =
      orderedFamilyCommonOpenPowerMap f U n := by
  change orderedFamilyMap (U.ι ≫ f) (V.ι ≫ f) (commonOpenFamilyInclusion f h) n ≫
    orderedFamilyMap (V.ι ≫ f) f (Over.homMk V.ι rfl) n =
      orderedFamilyMap (U.ι ≫ f) f (Over.homMk U.ι rfl) n
  rw [← orderedFamilyMap_comp]
  apply congrArg (fun a ↦ orderedFamilyMap (U.ι ≫ f) f a n)
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X h

/-- Identity open inclusion induces the identity tuple-chart morphism. -/
theorem commonOpenPowerInclusion_id (U : X.Opens) (n : ℕ) :
    commonOpenPowerInclusion f (le_refl U) n = 𝟙 (orderedFamilyPowerOver (U.ι ≫ f) n) := by
  change orderedFamilyMap (U.ι ≫ f) (U.ι ≫ f) (commonOpenFamilyInclusion f (le_refl U)) n = _
  rw [commonOpenFamilyInclusion_id, orderedFamilyMap_id]

/-- The actual tuple-chart inclusions respect composition. -/
theorem commonOpenPowerInclusion_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (n : ℕ) :
    commonOpenPowerInclusion f hUV n ≫ commonOpenPowerInclusion f hVW n =
      commonOpenPowerInclusion f (hUV.trans hVW) n := by
  change orderedFamilyMap (U.ι ≫ f) (V.ι ≫ f) (commonOpenFamilyInclusion f hUV) n ≫
    orderedFamilyMap (V.ι ≫ f) (W.ι ≫ f) (commonOpenFamilyInclusion f hVW) n =
      orderedFamilyMap (U.ι ≫ f) (W.ι ≫ f) (commonOpenFamilyInclusion f (hUV.trans hVW)) n
  rw [← orderedFamilyMap_comp, commonOpenFamilyInclusion_comp]

end AllCharacteristics
