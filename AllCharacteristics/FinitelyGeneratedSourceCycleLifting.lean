import AllCharacteristics.FinitelyGeneratedDVRLifting
import AllCharacteristics.DVRSourceCycleLifting

/-!
# Constructed mixed-characteristic lifting of signed hypersurface cycles

Over finitely generated fields of positive characteristic, the base ring,
smooth projective lift, and generic signed cycle are all constructed. The
cycle has exactly its original degree, including any negative coefficients
and inseparable residue extensions. No existence of a Cohen ring is assumed.
-/

open AlgebraicGeometry IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A smooth homogeneous hypersurface and any signed zero-cycle over a
finitely generated field of positive characteristic lift to a constructed
complete characteristic-zero DVR, preserving the exact signed degree. -/
theorem exists_smooth_charZero_lift_with_zeroCycle_fg_positive
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    {σ : Type} [Finite σ] (p : MvPolynomial σ k) {d : ℕ}
    (hp : p.IsHomogeneous d) (hne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (maximalIdeal R) R) (_ : CharZero R) (b : R →+* k),
      Function.Surjective b ∧ ∃ q : MvPolynomial σ R, ∃ hq : q.IsHomogeneous d,
        q.map b = p ∧ Smooth (hypersurfaceToBase q hq) ∧
        Smooth (hypersurfaceToBase (q.map (algebraMap R (FractionRing R)))
          (hq.map (algebraMap R (FractionRing R)))) ∧
        ∃ w : ZeroCycle (hypersurface (q.map (algebraMap R (FractionRing R)))
          (hq.map (algebraMap R (FractionRing R)))),
          ZeroCycle.degree (hypersurfaceToBase (q.map (algebraMap R (FractionRing R)))
            (hq.map (algebraMap R (FractionRing R)))) w =
            ZeroCycle.degree (hypersurfaceToBase p hp) z := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hasCompleteCharZeroDVRLift_of_fg_positive ℓ k
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, b, hb, ?_⟩
  exact exists_smooth_lift_with_zeroCycle b hb (algebraMap R (FractionRing R)) p hp hne z

end AllCharacteristics
