import AllCharacteristics.ClosedSpecialFiberSmoothNeighborhood
import AllCharacteristics.ResidueFiberSmoothness
import AllCharacteristics.SurjectiveResiduePresentation

/-! SOURCE ONLY / UNVERIFIED. Pointwise special-fiber smoothness implies
relative smoothness for a flat family over a local ring. The proof restricts
to an actual open around the SAME point, never assumes the whole fiber smooth. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u

theorem smooth_closed_fiber_of_smooth_surjective_pullback
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (b : R →+* k) (hb : Function.Surjective b)
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom b)))] :
    Smooth (f.fiberToSpecResidueField (closedPoint R)) := by
  let e := residueEquivOfSurjective b hb
  have he : CommRingCat.ofHom b ≫ CommRingCat.ofHom e.symm.toRingHom =
      CommRingCat.ofHom (residue R) := by
    ext r
    exact e.symm_apply_eq.mpr (residueEquivOfSurjective_residue b hb r).symm
  letI : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (residue R)))) := by
    rw [← he, Spec.map_comp, ← pullbackLeftPullbackSndIso_inv_snd_snd]
    infer_instance
  exact smooth_closed_fiber_of_smooth_residue_pullback R f

/-- The image of a field-valued surjection is the actual closed base point. -/
theorem spec_surjective_field_closedPoint
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) :
    Spec.map (CommRingCat.ofHom b) (closedPoint k) = closedPoint R := by
  apply PrimeSpectrum.ext
  change Ideal.comap b (maximalIdeal k) = maximalIdeal R
  rw [maximalIdeal_eq_bot, Ideal.comap_bot]
  exact IsLocalRing.ker_eq_maximalIdeal b hb

/-- Genuine same-point implication. The only geometry inputs are the actual
Cartesian closed fiber, flatness, finite presentation, and pointwise smoothness
in that fiber. The final pencil wrapper derives those structural inputs. -/
theorem mem_smoothLocus_of_smooth_point_in_surjective_specialFiber
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [Flat f] [LocallyOfFinitePresentation f]
    (j : Y ⟶ X) [IsClosedImmersion j]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation g]
    (b : R →+* k) (hb : Function.Surjective b)
    (H : IsPullback j g f (Spec.map (CommRingCat.ofHom b)))
    (y : Y) (hy : y ∈ g.smoothLocus) : j y ∈ f.smoothLocus := by
  let V := closedSpecialFiberSmoothAmbientOpen j g
  have hpre : j ⁻¹ᵁ V = g.smoothLocus :=
    closedSpecialFiberSmoothAmbientOpen_preimage j g
  let z : (j ⁻¹ᵁ V).toScheme := ⟨y, by change y ∈ j ⁻¹ᵁ V; rw [hpre]; exact hy⟩
  let xV : V.toScheme := (j ∣_ V) z
  let fV := V.ι ≫ f
  have hxy : V.ι xV = j y := by
    exact Scheme.Hom.congr_app (morphismRestrict_ι j V) z
  have hbase : fV xV = closedPoint R := by
    change f (V.ι xV) = _
    rw [hxy]
    have h := Scheme.Hom.congr_app H.w y
    change f (j y) = Spec.map (CommRingCat.ofHom b) (g y) at h
    rw [h, Subsingleton.elim (g y) (closedPoint k)]
    exact spec_surjective_field_closedPoint b hb
  letI : Smooth (pullback.snd fV (Spec.map (CommRingCat.ofHom b))) :=
    closedSpecialFiberSmoothAmbientOpen_pullback_smooth f j g b H
  have hsmFiber : Smooth (fV.fiberToSpecResidueField (fV xV)) := by
    rw [hbase]
    exact smooth_closed_fiber_of_smooth_surjective_pullback fV b hb
  have hx := mem_smoothLocus_of_smooth_fiber_over_affine fV xV hsmFiber
  change xV ∈ (V.ι ≫ f).smoothLocus at hx
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hx
  change V.ι xV ∈ f.smoothLocus at hx
  rwa [hxy] at hx

end AllCharacteristics
