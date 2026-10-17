import AllCharacteristics.FiniteFieldLifting
import AllCharacteristics.SmoothAlgebraPointLifting
import AllCharacteristics.FiniteFreeAmbientFiber

/-!
# Degree-preserving lifting of finite points on smooth families

A finite residue-field point of a smooth separated family over a complete local
ring supplies an effective cycle of the same degree on every field-valued
fiber. The proof constructs a finite free complete local coefficient algebra,
lifts the actual point, and pushes forward its fiber cycle. Inseparable
extension degrees are retained throughout.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- Lift a finite residue-field point to an actual point valued in a complete
local finite free algebra, retaining its exact reduction and degree. -/
theorem lift_smooth_finite_point
    {R k L : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : IsLocalRing A)
      (_ : Module.Free R A) (_ : Module.Finite R A)
      (_ : IsAdicComplete (maximalIdeal A) A) (c : A →+* L)
      (s : Spec (.of A) ⟶ X),
      Function.Surjective c ∧ Module.finrank R A = Module.finrank k L ∧
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom c) ≫ s = q := by
  obtain ⟨A, _, _, _, _, _, _, c, hc, hcomm, hrank, _⟩ :=
    hasCompleteLocalLift_of_finite_extension (L := L) b hb
  have hcoef : c.comp (algebraMap R A) = (algebraMap k L).comp b := RingHom.ext hcomm
  obtain ⟨s, hs, hred⟩ := lift_smooth_point_to_complete_local_algebra f c hc q
    (by rw [hcoef]; exact hq)
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, c, s, hc, hrank, hs, hred⟩

/-- A finite special point of a smooth separated family gives a cycle of its
full extension degree on any field-valued fiber. -/
theorem exists_effectiveZeroCycle_fiber_of_smooth_finite_point
    {R k L K : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field L] [Field K]
    [Algebra k L] [Module.Finite k L]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsSeparated f]
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)))
    (g : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f g),
      EffectiveZeroCycle.degree (pullback.snd f g) z = Module.finrank k L := by
  obtain ⟨A, _, _, _, _, _, _, _, s, _, hrank, hs, _⟩ :=
    lift_smooth_finite_point b hb f q hq
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_fiber_of_finite_free_point f s hs g
  exact ⟨z, hz.trans hrank⟩

end AllCharacteristics
