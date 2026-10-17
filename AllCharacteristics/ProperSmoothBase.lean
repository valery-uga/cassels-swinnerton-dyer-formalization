import AllCharacteristics.SmoothSpecialFiber

/-!
# The maximal smooth base of a proper family

The complement of the image of the nonsmooth locus is open. Restricting the
family to this open gives a smooth morphism, and it is the largest base open
with that property. This construction does not identify smooth fibers with
smoothness of the original morphism unless the needed flatness is supplied.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- Restriction to a base open is smooth exactly when every point above that
open is in the original morphism's smooth locus. -/
theorem smooth_morphismRestrict_iff_preimage_le_smoothLocus (U : Y.Opens) :
    Smooth (f ∣_ U) ↔ f ⁻¹ᵁ U ≤ f.smoothLocus := by
  constructor
  · intro h
    have hc : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    have ht := ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus_eq_top
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at ht
    intro x hx
    exact ht.ge (show (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) from trivial)
  · intro h
    have hc : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
      apply Scheme.Hom.smoothLocus_eq_top_iff.mp
      rw [← Scheme.Hom.preimage_smoothLocus_eq]
      apply top_unique
      intro x _
      exact h x.2
    have ht : Smooth ((f ∣_ U) ≫ U.ι) := by
      rw [morphismRestrict_ι]
      exact hc
    have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
      MorphismProperty.respectsIso_of_isStableUnderComposition
        (fun _ _ _ (h : IsIso _) ↦ by infer_instance)
    have : MorphismProperty.HasOfPostcompProperty (@Smooth.{u}) (@IsOpenImmersion.{u}) :=
      hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (@Smooth.{u})
        (fun _ _ hf ↦ by have := hf; infer_instance)
    exact MorphismProperty.of_postcomp (@Smooth.{u}) (W' := @IsOpenImmersion.{u})
      (f ∣_ U) U.ι inferInstance ht

/-- The largest base open above which the entire proper family is smooth. -/
noncomputable def properSmoothBase [UniversallyClosed f] : Y.Opens :=
  ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

/-- A base point is in the smooth base exactly when every point above it is
in the original morphism's smooth locus. -/
theorem mem_properSmoothBase_iff [UniversallyClosed f] (y : Y) :
    y ∈ properSmoothBase f ↔ ∀ x : X, f x = y → x ∈ f.smoothLocus := by
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x, hn, hx⟩
  · intro h ⟨x, hx, he⟩
    exact hx (h x he)

/-- A base open lies in the smooth base exactly when its inverse image lies
in the smooth locus of the original family. -/
theorem le_properSmoothBase_iff [UniversallyClosed f] (U : Y.Opens) :
    U ≤ properSmoothBase f ↔ f ⁻¹ᵁ U ≤ f.smoothLocus := by
  constructor
  · intro h x hx
    exact (mem_properSmoothBase_iff f (f x)).mp (h hx) x rfl
  · intro h y hy
    apply (mem_properSmoothBase_iff f y).mpr
    intro x hx
    apply h
    change f x ∈ U
    rwa [hx]

/-- The smooth base is the largest open over which restriction is smooth. -/
theorem smooth_morphismRestrict_iff_le_properSmoothBase [UniversallyClosed f] (U : Y.Opens) :
    Smooth (f ∣_ U) ↔ U ≤ properSmoothBase f :=
  (smooth_morphismRestrict_iff_preimage_le_smoothLocus f U).trans
    (le_properSmoothBase_iff f U).symm

/-- Restricting a proper family to its smooth base is smooth. -/
theorem smooth_on_properSmoothBase [UniversallyClosed f] :
    Smooth (f ∣_ properSmoothBase f) :=
  (smooth_morphismRestrict_iff_le_properSmoothBase f _).mpr le_rfl

omit [LocallyOfFinitePresentation f] in
/-- A base change factoring through an open where the family is smooth has
a smooth pullback, with its actual scheme pullback retained. -/
theorem smooth_pullback_of_factor_through_smooth_open
    (U : Y.Opens) [Smooth (f ∣_ U)] {Z : Scheme.{u}} (g : Z ⟶ U.toScheme) :
    Smooth (pullback.snd f (g ≫ U.ι)) := by
  have hp := (IsPullback.of_hasPullback (f ∣_ U) g).paste_horiz
    (isPullback_morphismRestrict f U).flip
  rw [← hp.isoPullback_inv_snd]
  infer_instance

/-- Every morphism whose image lies in the proper smooth base gives a smooth
base-changed family. -/
theorem smooth_pullback_of_range_subset_properSmoothBase [UniversallyClosed f]
    {Z : Scheme.{u}} (g : Z ⟶ Y) (hg : Set.range g ⊆ properSmoothBase f) :
    Smooth (pullback.snd f g) := by
  have := smooth_on_properSmoothBase f
  have hr : Set.range g ⊆ Set.range (properSmoothBase f).ι := by
    rwa [(properSmoothBase f).range_ι]
  let gU := IsOpenImmersion.lift (properSmoothBase f).ι g hr
  have he : gU ≫ (properSmoothBase f).ι = g := IsOpenImmersion.lift_fac _ _ _
  rw [← he]
  exact smooth_pullback_of_factor_through_smooth_open f (properSmoothBase f) gU

/-- Every residue-field fiber over the smooth base is smooth. -/
theorem smooth_fiber_of_mem_properSmoothBase [UniversallyClosed f]
    (y : Y) (hy : y ∈ properSmoothBase f) : Smooth (f.fiberToSpecResidueField y) := by
  apply smooth_pullback_of_range_subset_properSmoothBase f
  rw [Scheme.range_fromSpecResidueField]
  exact Set.singleton_subset_iff.mpr hy

/-- For a flat proper family over an affine base, membership in the smooth
base is equivalent to smoothness of the entire residue-field fiber. -/
theorem mem_properSmoothBase_iff_smooth_fiber
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f] (y : Spec R) :
    y ∈ properSmoothBase f ↔ Smooth (f.fiberToSpecResidueField y) := by
  refine ⟨smooth_fiber_of_mem_properSmoothBase f y, ?_⟩
  intro h
  apply (mem_properSmoothBase_iff f y).mpr
  intro x hx
  apply mem_smoothLocus_of_smooth_fiber_over_affine f x
  rwa [hx]

end AllCharacteristics
