import AllCharacteristics.FiniteFlatCycle
import AllCharacteristics.ProperCyclePushforward

/-!
# Fiber cycles from finite free algebra points

A morphism from a finite free algebra into a separated family supplies cycles
of its free rank on every field-valued fiber. The morphism need not be a closed
immersion: weighted pushforward retains the full degree.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- A point with values in a finite free coefficient algebra supplies an
actual cycle of its free rank on every field-valued ambient fiber. -/
theorem exists_effectiveZeroCycle_fiber_of_finite_free_point
    {R A k : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
    (q : Spec (.of A) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (b : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f b),
      EffectiveZeroCycle.degree (pullback.snd f b) z = Module.finrank R A := by
  have : IsFinite (q ≫ f) := by
    rw [hq]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (q ≫ f) := by
    rw [hq]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : IsFinite q := IsFinite.of_comp q f
  let e := pullbackRightPullbackFstIso f b q
  let qb := e.inv ≫ pullback.snd q (pullback.fst f b)
  have : IsFinite qb := by dsimp only [qb]; infer_instance
  have hcomp : qb ≫ pullback.snd f b = pullback.snd (q ≫ f) b :=
    (Category.assoc _ _ _).trans (pullbackRightPullbackFstIso_inv_snd_snd f b q)
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_finite_flat_baseChange (q ≫ f) b
  refine ⟨pushforwardCycle qb z, ?_⟩
  rw [degree_pushforwardCycle, hcomp, hz, hq]
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R A _).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := A)) _)

end AllCharacteristics
