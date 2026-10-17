import AllCharacteristics.SmoothFinitePointLifting
import AllCharacteristics.ClosedPointAlgebra

/-!
# Lifting closed-point degrees to other fibers

An actual closed point of the special fiber of a smooth separated family over
a complete local ring supplies an effective cycle on every field-valued fiber
of the same full residue degree. This is the degree-preserving lifting step;
it does not require a separable point or an embedded lifted subscheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- Every actual closed special-fiber point supplies an effective cycle of
its full residue degree on each field-valued fiber of the smooth family. -/
theorem exists_effectiveZeroCycle_fiber_of_smooth_closedPoint
    {R k K : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k] [Field K]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsSeparated f]
    (x : closedPoints (pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u}))
    (g : Spec (.of K) ⟶ Spec (.of R)) :
    ∃ z : EffectiveZeroCycle (pullback f g),
      EffectiveZeroCycle.degree (pullback.snd f g) z =
        (pullback.snd f (Spec.map (CommRingCat.ofHom b))).residueDegree x.1 := by
  let b0 := Spec.map (CommRingCat.ofHom b)
  let X0 := pullback f b0
  let f0 := pullback.snd f b0
  let L := X0.residueField x.1
  let : Algebra k L := pointAlgebra f0 x.1
  have : Module.Finite k L := closedPoint_moduleFinite f0 x
  let q := X0.fromSpecResidueField x.1 ≫ pullback.fst f b0
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      X0.fromSpecResidueField x.1 ≫ f0 := pointAlgebra_spec f0 x.1
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
    calc
      q ≫ f = X0.fromSpecResidueField x.1 ≫ (pullback.fst f b0 ≫ f) := Category.assoc _ _ _
      _ = X0.fromSpecResidueField x.1 ≫ (f0 ≫ b0) := by rw [pullback.condition]
      _ = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ b0 := by
        rw [← Category.assoc, ← ha]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
        rw [← Spec.map_comp]
        rfl
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_fiber_of_smooth_finite_point (L := L) b hb f q hq g
  exact ⟨z, hz.trans (closedPoint_finrank_eq_residueDegree f0 x)⟩

end AllCharacteristics
