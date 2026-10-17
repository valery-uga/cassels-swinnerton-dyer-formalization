import AllCharacteristics.HypersurfaceReduction
import AllCharacteristics.DVRHypersurfaceLifting
import AllCharacteristics.SmoothFiniteSubschemeLifting
import AllCharacteristics.ClosedPointAlgebra

/-!
# Embedded lifting from the original residue hypersurface

A closed point on the specified residue equation lifts as a finite flat closed
subscheme of the constructed smooth family. Global projective base change
identifies the source hypersurface itself, and a Cartesian square retains the
original closed point's embedding. This proves the geometric lifting assertion
over any given complete DVR with the prescribed residue field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
section CompleteLocal
variable {R k : Type u} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field k]
variable {σ : Type} [Finite σ]

/-- A closed point on a specified reduced equation lifts as an embedded
finite flat subscheme of the given smooth family, with its exact source
embedding recovered by base change. -/
theorem exists_finite_flat_subscheme_of_reduced_closedPoint
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (he : q.map b = p)
    [Smooth (hypersurfaceToBase q hq)] (x : closedPoints (hypersurface p hp)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
      (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
      IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
      Flat (i ≫ hypersurfaceToBase q hq) ∧
      (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
        (hypersurfaceToBase p hp).residueDegree x.1) ∧
      IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
        i (hypersurfaceReductionMap b q hq p hp he) := by
  let L := (hypersurface p hp).residueField x.1
  let : Algebra k L := pointAlgebra (hypersurfaceToBase p hp) x.1
  have : Module.Finite k L := closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  let q0 := (hypersurface p hp).fromSpecResidueField x.1
  have : IsClosedImmersion q0 := isClosed_singleton_iff_isClosedImmersion.mp x.2
  have : IsClosedImmersion (hypersurfaceReductionMap b q hq p hp he) :=
    isClosedImmersion_hypersurfaceReductionMap b q hq p hp he hb
  let a := q0 ≫ hypersurfaceReductionMap b q hq p hp he
  have : IsClosedImmersion a := by dsimp only [a]; infer_instance
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      q0 ≫ hypersurfaceToBase p hp := pointAlgebra_spec (hypersurfaceToBase p hp) x.1
  have hac : a ≫ hypersurfaceToBase q hq =
      Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
    change (q0 ≫ hypersurfaceReductionMap b q hq p hp he) ≫ hypersurfaceToBase q hq = _
    rw [Category.assoc, hypersurfaceReductionMap_toBase, ← Category.assoc, ← ha,
      ← Spec.map_comp]
    rfl
  obtain ⟨Z, i, j, hi, hfinite, hflat, hrank, hred, hpull⟩ :=
    exists_finite_flat_closed_subscheme_of_smooth_finite_point (L := L)
      b hb (hypersurfaceToBase q hq) a hac
  refine ⟨Z, i, j, hi, hfinite, hflat, ?_, ?_⟩
  · intro r
    exact (hrank r).trans (closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) x)
  · apply (IsPullback.paste_vert_iff
      (isPullback_hypersurfaceReductionMap b q hq p hp he) hred).mp
    rw [← ha]
    exact hpull

end CompleteLocal

section CompleteDVR
variable {R k : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field k]
variable {σ : Type} [Finite σ]

/-- Over a given complete DVR with prescribed residue field, a smooth nonzero
homogeneous equation and any closed point lift together to a smooth family
and an embedded finite flat subscheme of exactly the point's residue degree. -/
theorem exists_smooth_lift_with_closed_subscheme
    (b : R →+* k) (hb : Function.Surjective b)
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : closedPoints (hypersurface p hp)) :
    ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d, ∃ he : q.map b = p,
      Smooth (hypersurfaceToBase q hq) ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
        (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
        IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
        Flat (i ≫ hypersurfaceToBase q hq) ∧
        (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
          (hypersurfaceToBase p hp).residueDegree x.1) ∧
        IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
          i (hypersurfaceReductionMap b q hq p hp he) := by
  obtain ⟨q, hq, he, hs⟩ := exists_smooth_homogeneous_lift_of_surjective b hb p hp hne
  have := hs
  obtain ⟨Z, i, j, hi, hfinite, hflat, hrank, hpull⟩ :=
    exists_finite_flat_subscheme_of_reduced_closedPoint b hb q hq p hp he x
  exact ⟨q, hq, he, hs, Z, i, j, hi, hfinite, hflat, hrank, hpull⟩

end CompleteDVR
end AllCharacteristics
