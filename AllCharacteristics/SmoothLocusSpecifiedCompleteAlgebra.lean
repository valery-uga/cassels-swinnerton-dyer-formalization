import AllCharacteristics.SmoothAlgebraPointLifting

/-! SOURCE ONLY / UNVERIFIED. Lift into the SPECIFIED complete local algebra,
with the GIVEN point as exact reduction. No finite/free algebra is chosen. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u

theorem lift_smoothLocus_point_to_specified_complete_local_algebra
    {R A L : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Field L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
    (d : A →+* L) (hd : Function.Surjective d)
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (d.comp (algebraMap R A))))
    (hsm : q (IsLocalRing.closedPoint L) ∈ f.smoothLocus) :
    ∃ s : Spec (.of A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom d) ≫ s = q := by
  have hrange : Set.range q ⊆ Set.range f.smoothLocus.ι := by
    rw [f.smoothLocus.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    change q x ∈ f.smoothLocus
    rw [hx]
    exact hsm
  let qU := IsOpenImmersion.lift f.smoothLocus.ι q hrange
  have hqU : qU ≫ (f.smoothLocus.ι ≫ f) =
      Spec.map (CommRingCat.ofHom (d.comp (algebraMap R A))) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hq]
  letI : Smooth (f.smoothLocus.ι ≫ f) := smooth_on_smoothLocus f
  obtain ⟨s, hs, hred⟩ := lift_smooth_point_to_complete_local_algebra
    (f.smoothLocus.ι ≫ f) d hd qU hqU
  refine ⟨s ≫ f.smoothLocus.ι, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred]
    exact IsOpenImmersion.lift_fac _ _ _

end AllCharacteristics
