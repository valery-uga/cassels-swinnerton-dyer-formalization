import AllCharacteristics.SmoothFiniteSubschemeLifting
import AllCharacteristics.ClosedPointAlgebra

/-!
# Lifting an actual special-fiber closed point as a finite flat subscheme

This is the embedded form of the degree-preserving lifting argument. The
special fiber is identified by a Cartesian square with the original closed
point's residue-field immersion, rather than only by an equality of degrees.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- A closed point of the special fiber of a smooth separated family over a
complete local ring lifts to a finite flat closed subscheme of its full degree.
The pullback square identifies the special fiber with the original embedded
point, including inseparable residue extensions. -/
theorem exists_finite_flat_closed_subscheme_of_smooth_closedPoint
    {R k : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [IsSeparated f]
    (x : closedPoints (pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X)
      (j : Spec (.of ((pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u}).residueField
        x.1)) ⟶ Z),
      IsClosedImmersion i ∧ IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧
      (∀ r, (i ≫ f).finrank r =
        (pullback.snd f (Spec.map (CommRingCat.ofHom b))).residueDegree x.1) ∧
      IsPullback j
        ((pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u}).fromSpecResidueField x.1)
        i (pullback.fst f (Spec.map (CommRingCat.ofHom b))) := by
  let b0 := Spec.map (CommRingCat.ofHom b)
  let X0 := pullback f b0
  let f0 := pullback.snd f b0
  let L := X0.residueField x.1
  let : Algebra k L := pointAlgebra f0 x.1
  have : Module.Finite k L := closedPoint_moduleFinite f0 x
  let q0 := X0.fromSpecResidueField x.1
  have : IsClosedImmersion q0 := isClosed_singleton_iff_isClosedImmersion.mp x.2
  have : IsClosedImmersion b0 := IsClosedImmersion.spec_of_surjective _ hb
  let q := q0 ≫ pullback.fst f b0
  have : IsClosedImmersion q := by dsimp only [q]; infer_instance
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k L)) = q0 ≫ f0 :=
    pointAlgebra_spec f0 x.1
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
    calc
      q ≫ f = q0 ≫ (pullback.fst f b0 ≫ f) := Category.assoc _ _ _
      _ = q0 ≫ (f0 ≫ b0) := by rw [pullback.condition]
      _ = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ b0 := by
        rw [← Category.assoc, ← ha]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap k L).comp b)) := by
        rw [← Spec.map_comp]
        rfl
  obtain ⟨Z, i, j, hi, hfinite, hflat, hrank, hred, hpull⟩ :=
    exists_finite_flat_closed_subscheme_of_smooth_finite_point (L := L) b hb f q hq
  refine ⟨Z, i, j, hi, hfinite, hflat, ?_, ?_⟩
  · intro r
    exact (hrank r).trans (closedPoint_finrank_eq_residueDegree f0 x)
  · apply (IsPullback.paste_vert_iff (.of_hasPullback f b0) hred).mp
    rw [← ha]
    exact hpull

end AllCharacteristics
