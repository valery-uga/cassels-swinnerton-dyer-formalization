import AllCharacteristics.ProperSmoothBase

/-!
# The smooth-fiber criterion on a flat base neighborhood

It is enough for a family to be flat over an open neighborhood of the fiber
under consideration. Restricting the source preserves smoothness of that
fiber; the affine-base criterion then applies to the restricted source.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- Restricting the source to an open subscheme preserves smoothness of a
fiber, with the original residue-field base retained. -/
theorem smooth_fiber_comp_openImmersion
    {X Y V : Scheme.{u}} (f : X ⟶ Y) (i : V ⟶ X) [IsOpenImmersion i] (x : V)
    (hsm : Smooth (f.fiberToSpecResidueField ((i ≫ f) x))) :
    Smooth ((i ≫ f).fiberToSpecResidueField ((i ≫ f) x)) := by
  have hopen : Smooth (pullback.snd i
      (pullback.fst f (Y.fromSpecResidueField ((i ≫ f) x)))) := by infer_instance
  have hiso : Smooth ((pullbackRightPullbackFstIso f
      (Y.fromSpecResidueField ((i ≫ f) x)) i).inv) := by infer_instance
  rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
  exact @smooth_comp _ _ _ _ _ hiso (@smooth_comp _ _ _ _ _ hopen hsm)

/-- A smooth fiber above a flat base neighborhood lies in the smooth locus
of the original morphism. Global flatness is not required. -/
theorem mem_smoothLocus_of_smooth_fiber_on_flat_open
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] (U : (Spec R).Opens) [Flat (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hsm : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  let q : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  let g := (f ⁻¹ᵁ U).ι ≫ f
  have : Flat g := by
    change Flat ((f ⁻¹ᵁ U).ι ≫ f)
    rw [← morphismRestrict_ι]
    infer_instance
  have hq := mem_smoothLocus_of_smooth_fiber_over_affine g q
    (smooth_fiber_comp_openImmersion f (f ⁻¹ᵁ U).ι q hsm)
  change q ∈ ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus at hq
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hq
  exact hq

/-- A smooth fiber over a flat base neighborhood belongs to the maximal
smooth base open of a proper family. -/
theorem mem_properSmoothBase_of_smooth_fiber_on_flat_open
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (U : (Spec R).Opens) [Flat (f ∣_ U)] (y : Spec R) (hy : y ∈ U)
    (hsm : Smooth (f.fiberToSpecResidueField y)) : y ∈ properSmoothBase f := by
  apply (mem_properSmoothBase_iff f y).mpr
  intro x hx
  apply mem_smoothLocus_of_smooth_fiber_on_flat_open f U x
  · rwa [hx]
  · rwa [hx]

end AllCharacteristics
