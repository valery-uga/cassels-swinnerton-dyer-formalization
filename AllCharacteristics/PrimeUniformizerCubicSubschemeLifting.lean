import AllCharacteristics.CohenPrimeUniformizerExistence
import AllCharacteristics.DVRSourceSubschemeLifting

/-! Retain the literal Cohen prime uniformizer in the SAME base ring used
for the smooth cubic and original closed-point lifting construction.
This does not assert Hilbert representability or a Hilbert-scheme R-point. -/
open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
universe u

theorem exists_prime_uniformizer_smooth_cubic_lift_with_original_closed_subscheme
    {k : Type u} [Field k]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
      (b : R →+* k), Function.Surjective b ∧
      IsLocalRing.maximalIdeal R = Ideal.span {(ℓ : R)} ∧
      RingHom.ker b = Ideal.span {(ℓ : R)} ∧
      (∃ e : IsLocalRing.ResidueField R ≃+* k,
        ∀ r, e (IsLocalRing.residue R r) = b r) ∧
      ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
        ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
        ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
          (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
          IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
          Flat (i ≫ hypersurfaceToBase q hq) ∧
          (∀ r, (i ≫ hypersurfaceToBase q hq).finrank r =
            (hypersurfaceToBase p hp).residueDegree x.1) ∧
          IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
            i (hypersurfaceReductionMap b q hq p hp he) := by
  obtain ⟨R, _, _, _, _, _, b, hb, hmax, hker, hequiv⟩ :=
    exists_completeDVR_prime_uniformizer ℓ k
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, hmax, hker, hequiv, ?_⟩
  exact exists_smooth_lift_with_closed_subscheme b hb p hp hne x

end AllCharacteristics
