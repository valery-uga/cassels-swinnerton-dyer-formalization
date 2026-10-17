import AllCharacteristics.SmoothPointLifting
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! SOURCE ONLY / UNVERIFIED. An open smooth neighborhood in a CLOSED
special fiber is the intersection with an actual open in the total family.
No smoothness of the entire special fiber is used. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

def closedSpecialFiberSmoothAmbientOpen
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (j : Y ⟶ X) [IsClosedImmersion j]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation g] : X.Opens :=
  ⟨(j '' (g.smoothLocus : Set Y)ᶜ)ᶜ,
    (j.isClosedEmbedding.isClosedMap _
      g.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

theorem closedSpecialFiberSmoothAmbientOpen_preimage
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (j : Y ⟶ X) [IsClosedImmersion j]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation g] :
    j ⁻¹ᵁ closedSpecialFiberSmoothAmbientOpen j g = g.smoothLocus := by
  ext y
  change j y ∉ j '' (g.smoothLocus : Set Y)ᶜ ↔ y ∈ g.smoothLocus
  constructor
  · intro hy
    by_contra hny
    exact hy ⟨y, hny, rfl⟩
  · intro hy
    rintro ⟨z, hz, hzy⟩
    have he : z = y := j.isClosedEmbedding.injective hzy
    subst z
    exact hz hy

/-- Restrict the ACTUAL Cartesian special fiber to the above open. Its
coefficient projection is smooth even if other points of Y are singular. -/
theorem closedSpecialFiberSmoothAmbientOpen_pullback_smooth
    {R k : Type u} [CommRing R] [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (j : Y ⟶ X) [IsClosedImmersion j]
    (g : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation g]
    (b : R →+* k)
    (H : IsPullback j g f (Spec.map (CommRingCat.ofHom b))) :
    Smooth (pullback.snd
      ((closedSpecialFiberSmoothAmbientOpen j g).ι ≫ f)
      (Spec.map (CommRingCat.ofHom b))) := by
  let V := closedSpecialFiberSmoothAmbientOpen j g
  have hpre : j ⁻¹ᵁ V = g.smoothLocus :=
    closedSpecialFiberSmoothAmbientOpen_preimage j g
  letI : Smooth ((j ⁻¹ᵁ V).ι ≫ g) := by
    rw [hpre]
    exact smooth_on_smoothLocus g
  have HC : IsPullback (j ∣_ V) ((j ⁻¹ᵁ V).ι ≫ g)
      (V.ι ≫ f) (Spec.map (CommRingCat.ofHom b)) :=
    ((isPullback_morphismRestrict j V).flip.paste_horiz H.flip).flip
  rw [← HC.isoPullback_inv_snd]
  infer_instance

end AllCharacteristics
