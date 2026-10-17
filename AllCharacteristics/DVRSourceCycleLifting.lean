import AllCharacteristics.DVRHypersurfaceLifting
import AllCharacteristics.HypersurfaceCycleLifting
import AllCharacteristics.HypersurfaceFiberCycles

/-!
# Smooth lifting with cycles from the original hypersurface

Over a given complete DVR with a prescribed residue field, a nonzero smooth
homogeneous hypersurface and any effective or signed zero-cycle lift together.
The target cycle lies on the projective hypersurface defined by the mapped
polynomial and has exactly the source cycle's degree. The smooth projective
family and the finite free point lifts are constructed inside the proof.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {R k K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field k] [Field K]
variable {σ : Type} [Finite σ]

/-- A smooth residue hypersurface with an effective cycle lifts to a smooth
family whose mapped equation has an effective cycle of the original degree. -/
theorem exists_smooth_lift_with_effectiveZeroCycle
    (b : R →+* k) (hb : Function.Surjective b) (g : R →+* K)
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp)) :
    ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d,
      q.map b = p ∧ Smooth (hypersurfaceToBase q hq) ∧
      Smooth (hypersurfaceToBase (q.map g) (hq.map g)) ∧
      ∃ w : EffectiveZeroCycle (hypersurface (q.map g) (hq.map g)),
        EffectiveZeroCycle.degree (hypersurfaceToBase (q.map g) (hq.map g)) w =
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z := by
  obtain ⟨q, hq, he, hs⟩ := exists_smooth_homogeneous_lift_of_surjective b hb p hp hne
  have := hs
  have hg := smooth_hypersurfaceToBase_map g q hq
  obtain ⟨v, hv⟩ := exists_effectiveZeroCycle_fiber_of_reduced_cycle b hb q hq p hp he z g
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_mapped_of_fiber_cycle q hq g v
  exact ⟨q, hq, he, hs, hg, w, hw.trans hv⟩

/-- Signed cycles lift with their exact degree, including negative source
coefficients and inseparable closed points. The target is the actual projective
hypersurface of the mapped polynomial, and both smoothness assertions are proved. -/
theorem exists_smooth_lift_with_zeroCycle
    (b : R →+* k) (hb : Function.Surjective b) (g : R →+* K)
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : ZeroCycle (hypersurface p hp)) :
    ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d,
      q.map b = p ∧ Smooth (hypersurfaceToBase q hq) ∧
      Smooth (hypersurfaceToBase (q.map g) (hq.map g)) ∧
      ∃ w : ZeroCycle (hypersurface (q.map g) (hq.map g)),
        ZeroCycle.degree (hypersurfaceToBase (q.map g) (hq.map g)) w =
        ZeroCycle.degree (hypersurfaceToBase p hp) z := by
  obtain ⟨q, hq, he, hs⟩ := exists_smooth_homogeneous_lift_of_surjective b hb p hp hne
  have := hs
  have hg := smooth_hypersurfaceToBase_map g q hq
  obtain ⟨v, hv⟩ := exists_zeroCycle_fiber_of_reduced_cycle b hb q hq p hp he z g
  obtain ⟨w, hw⟩ := exists_zeroCycle_mapped_of_fiber_cycle q hq g v
  exact ⟨q, hq, he, hs, hg, w, hw.trans hv⟩

end AllCharacteristics
