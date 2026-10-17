import AllCharacteristics.CoefficientPointTransfer
import AllCharacteristics.SmoothFinitePointLifting
import AllCharacteristics.CycleDegreeAssembly

/-!
# Lifting cycles from the original residue equation

A closed point of a reduced hypersurface supplies an effective cycle of the
same full residue degree on any fiber of its smooth lift over a complete local
ring. Applying this to the support gives exact degree preservation for both
effective and signed zero-cycles on the original residue hypersurface.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {R k K : Type u} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field k] [Field K]
variable {σ : Type} [Finite σ]

/-- A closed point on the reduced equation supplies a cycle on the actual
lifted fiber of exactly its original scheme residue degree. -/
theorem exists_effectiveZeroCycle_fiber_of_reduced_closedPoint
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hmap : q.map b = p)
    [Smooth (hypersurfaceToBase q hq)]
    (x : closedPoints (hypersurface p hp)) (g : R →+* K) :
    ∃ w : EffectiveZeroCycle
        (pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))),
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))) w =
      (hypersurfaceToBase p hp).residueDegree x.1 := by
  let L := (hypersurface p hp).residueField x.1
  let : Algebra k L := pointAlgebra (hypersurfaceToBase p hp) x.1
  have : Module.Finite k L := closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  obtain ⟨y, hy⟩ := pointOver_of_reduced_point b q hq p hp hmap x.1
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_fiber_of_smooth_finite_point
    (L := L) b hb (hypersurfaceToBase q hq) y hy (Spec.map (CommRingCat.ofHom g))
  exact ⟨w, hw.trans (closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) x)⟩

/-- Effective cycles on the original residue hypersurface lift to effective
cycles of exactly the same degree on every field-valued fiber. -/
theorem exists_effectiveZeroCycle_fiber_of_reduced_cycle
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hmap : q.map b = p)
    [Smooth (hypersurfaceToBase q hq)]
    (z : EffectiveZeroCycle (hypersurface p hp)) (g : R →+* K) :
    ∃ w : EffectiveZeroCycle
        (pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))),
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))) w =
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z := by
  apply exists_effectiveZeroCycle_of_support_replacements (hypersurfaceToBase p hp) _ z
  intro x _
  exact exists_effectiveZeroCycle_fiber_of_reduced_closedPoint b hb q hq p hp hmap x g

/-- Signed cycles on the original residue hypersurface lift with degree
unchanged. Negative coefficients and inseparable residue degrees are retained. -/
theorem exists_zeroCycle_fiber_of_reduced_cycle
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hmap : q.map b = p)
    [Smooth (hypersurfaceToBase q hq)]
    (z : ZeroCycle (hypersurface p hp)) (g : R →+* K) :
    ∃ w : ZeroCycle
        (pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))),
      ZeroCycle.degree
        (pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom g))) w =
      ZeroCycle.degree (hypersurfaceToBase p hp) z := by
  apply exists_zeroCycle_of_support_replacements (hypersurfaceToBase p hp) _ z
  intro x _
  exact exists_effectiveZeroCycle_fiber_of_reduced_closedPoint b hb q hq p hp hmap x g

end AllCharacteristics
