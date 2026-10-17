import AllCharacteristics.FinitelyGeneratedDVRLifting
import AllCharacteristics.DVRSourceSubschemeLifting

/-!
# Constructed mixed-characteristic embedded lifting

For every finitely generated field of positive characteristic, the lifting
base, smooth projective family, finite flat closed subscheme, and exact
special-fiber identification are all constructed. The residue field is the
original field and the degree includes its inseparable part.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A smooth homogeneous hypersurface and one of its closed points over a
finitely generated positive-characteristic field admit an actual embedded
mixed-characteristic lift with the same residue field and full degree. -/
theorem exists_smooth_charZero_lift_with_closed_subscheme_fg_positive
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    {σ : Type} [Finite σ] (p : MvPolynomial σ k) {d : ℕ}
    (hp : p.IsHomogeneous d) (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (maximalIdeal R) R) (_ : CharZero R) (b : R →+* k),
      Function.Surjective b ∧
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
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hasCompleteCharZeroDVRLift_of_fg_positive ℓ k
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, b, hb, ?_⟩
  exact exists_smooth_lift_with_closed_subscheme b hb p hp hne x

end AllCharacteristics
