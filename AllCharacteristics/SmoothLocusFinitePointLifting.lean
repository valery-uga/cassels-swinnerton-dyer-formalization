import AllCharacteristics.SmoothFinitePointLifting
import AllCharacteristics.SmoothPointLifting

/-!
# Degree-preserving lifting from the smooth locus

The smoothing argument for a singular cubic needs to lift only one smooth
closed point; the ambient special fiber need not be smooth.  This file gives
the corresponding local form of the finite-point lifting theorem by
restricting the family to its smooth locus.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics

universe u

/-- A finite residue point which lies in the smooth locus lifts to a point
over a finite free complete local algebra, with the same rank. -/
theorem lift_finite_point_in_smoothLocus
    {R k L : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)))
    (hsm : q (IsLocalRing.closedPoint L) ∈ f.smoothLocus) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
      (_ : Module.Free R A) (_ : Module.Finite R A)
      (_ : IsAdicComplete (maximalIdeal A) A) (c : A →+* L)
      (s : Spec (.of A) ⟶ X),
      Function.Surjective c ∧ Module.finrank R A = Module.finrank k L ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom c) ≫ s = q := by
  have hrange : Set.range q ⊆ Set.range f.smoothLocus.ι := by
    rw [f.smoothLocus.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    change q x ∈ f.smoothLocus
    rw [hx]
    exact hsm
  let qU := IsOpenImmersion.lift f.smoothLocus.ι q hrange
  have hqU : qU ≫ (f.smoothLocus.ι ≫ f) =
      Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hq]
  have : Smooth (f.smoothLocus.ι ≫ f) := smooth_on_smoothLocus f
  obtain ⟨A, _, _, _, _, _, _, c, sU, hc, hrank, hs, hred⟩ :=
    lift_smooth_finite_point b hb (f.smoothLocus.ι ≫ f) qU hqU
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, c, sU ≫ f.smoothLocus.ι, hc, hrank, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred]
    exact IsOpenImmersion.lift_fac _ _ _

/-- A finite special point in the smooth locus supplies an effective cycle of
the same degree on every field-valued fiber of a separated family. -/
theorem exists_effectiveZeroCycle_fiber_of_finite_point_in_smoothLocus
    {R k L K : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L] [Field K]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
    [IsSeparated f]
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)))
    (hsm : q (IsLocalRing.closedPoint L) ∈ f.smoothLocus)
    (g : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f g),
      EffectiveZeroCycle.degree (pullback.snd f g) z = Module.finrank k L := by
  obtain ⟨A, _, _, _, _, _, _, _, s, _, hrank, hs, _⟩ :=
    lift_finite_point_in_smoothLocus b hb f q hq hsm
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_fiber_of_finite_free_point f s hs g
  exact ⟨z, hz.trans hrank⟩

end AllCharacteristics
