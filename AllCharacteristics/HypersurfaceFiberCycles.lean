import AllCharacteristics.HomogeneousFiberCoordinates
import AllCharacteristics.CycleDegreeAssembly
import AllCharacteristics.ProperCyclePushforward

/-!
# Cycles on the hypersurface defined by the fiber equation

A cycle on the actual scheme-theoretic pullback supplies a cycle of the same
degree on the projective hypersurface defined by the mapped polynomial. The
construction uses actual residue-field points and finite pushforward, so it
retains inseparable degrees and works for signed as well as effective cycles.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} [Finite σ]

/-- Each closed point of an actual fiber supplies an effective cycle of its
full residue degree on the hypersurface defined by the mapped equation. -/
theorem exists_effectiveZeroCycle_mapped_of_fiber_closedPoint
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k)
    (x : closedPoints
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    ∃ w : EffectiveZeroCycle (hypersurface (p.map b) (hp.map b)),
      EffectiveZeroCycle.degree (hypersurfaceToBase (p.map b) (hp.map b)) w =
      (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))).residueDegree x.1 := by
  let Y := pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))
  let f := pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))
  let L := Y.residueField x.1
  let : Algebra k L := pointAlgebra f x.1
  have : Module.Finite k L := closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_fiber_residueField_coordinates p hp b x.1
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (algebraMap k L)
    (p.map b) (hp.map b) v hv he
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_of_finite_algebra_point (A := L)
    (hypersurfaceToBase (p.map b) (hp.map b)) a ha
  exact ⟨w, hw.trans (closedPoint_finrank_eq_residueDegree f x)⟩

/-- An effective cycle on the actual fiber gives an effective cycle of equal
degree on the projective hypersurface defined by its fiber equation. -/
theorem exists_effectiveZeroCycle_mapped_of_fiber_cycle
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k)
    (z : EffectiveZeroCycle
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)))) :
    ∃ w : EffectiveZeroCycle (hypersurface (p.map b) (hp.map b)),
      EffectiveZeroCycle.degree (hypersurfaceToBase (p.map b) (hp.map b)) w =
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z := by
  apply exists_effectiveZeroCycle_of_support_replacements
    (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) _ z
  intro x _
  exact exists_effectiveZeroCycle_mapped_of_fiber_closedPoint p hp b x

/-- Signed degree is preserved when passing from an actual fiber to the
hypersurface defined by its mapped homogeneous equation. -/
theorem exists_zeroCycle_mapped_of_fiber_cycle
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k)
    (z : ZeroCycle
      (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)))) :
    ∃ w : ZeroCycle (hypersurface (p.map b) (hp.map b)),
      ZeroCycle.degree (hypersurfaceToBase (p.map b) (hp.map b)) w =
      ZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z := by
  apply exists_zeroCycle_of_support_replacements
    (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) _ z
  intro x _
  exact exists_effectiveZeroCycle_mapped_of_fiber_closedPoint p hp b x

end AllCharacteristics
