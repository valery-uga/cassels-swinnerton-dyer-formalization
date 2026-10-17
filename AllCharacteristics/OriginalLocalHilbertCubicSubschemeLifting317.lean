import AllCharacteristics.CohenPrimeUniformizerExistence
import AllCharacteristics.DVRHypersurfaceLifting
import PfaffianDescent.OriginalHilbertCompleteLocalLift317

/-! SOURCE ONLY317. The original positive-characteristic closed point lifts
via the constructed Cohen DVR, smooth lifted cubic, and the genuine LOCAL
Hilbert smooth parameter and universal family. The final Hilbert prerequisite
is pending root acceptance. No global projective Hilbert scheme is assumed.
No alternative finite-free residue-algebra closed-subscheme lift is called. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equation transport to the SAME original point and reduction map.
The local Hilbert endpoint constructs the family. Equality elimination only
identifies the specified original residue polynomial with its exact lift map;
no family, smooth-point membership or reduction outcome is an input. -/
private theorem originalLocalHilbertFamily_of_equationReduction317
    {R k : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    (r : MvPolynomial (Fin 4) R) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : r.map b = p) (x : closedPoints (hypersurface p hp)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface r hr)
      (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
      IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase r hr) ∧
      Flat (i ≫ hypersurfaceToBase r hr) ∧
      (∀ y, (i ≫ hypersurfaceToBase r hr).finrank y =
        (hypersurfaceToBase p hp).residueDegree x.1) ∧
      IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
        i (hypersurfaceReductionMap b r hr p hp he) := by
  letI : Algebra R k := b.toAlgebra
  subst p
  exact PfaffianDescent.originalClosedPoint_hilbertFiniteFlatClosedSubscheme317
    R r hr k x hp0 hb

/-- Over the supplied complete DVR, construct the smooth lift and then
its original-point finiteflat closed family by LOCAL Hilbert classification.
DVR Noetherian/local dictionaries are derived, not new assumptions. -/
theorem exists_smooth_lift_with_closed_subscheme_viaLocalHilbert317
    {R k : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : closedPoints (hypersurface p hp)) :
    ∃ q : MvPolynomial (Fin 4) R, ∃ hq : q.IsHomogeneous 3,
      ∃ he : q.map b = p, Smooth (hypersurfaceToBase q hq) ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ hypersurface q hq)
        (j : Spec (.of ((hypersurface p hp).residueField x.1)) ⟶ Z),
        IsClosedImmersion i ∧ IsFinite (i ≫ hypersurfaceToBase q hq) ∧
        Flat (i ≫ hypersurfaceToBase q hq) ∧
        (∀ y, (i ≫ hypersurfaceToBase q hq).finrank y =
          (hypersurfaceToBase p hp).residueDegree x.1) ∧
        IsPullback j ((hypersurface p hp).fromSpecResidueField x.1)
          i (hypersurfaceReductionMap b q hq p hp he) := by
  obtain ⟨q, hq, he, hs⟩ := exists_smooth_homogeneous_lift_of_surjective b hb p hp hne
  letI : IsLocalRing R := inferInstance
  letI : IsNoetherianRing R := inferInstance
  letI : Smooth (hypersurfaceToBase q hq) := hs
  obtain ⟨Z, i, j, hi, hfinite, hflat, hrank, hpull⟩ :=
    originalLocalHilbertFamily_of_equationReduction317 b hb q hq p hp hne he x
  exact ⟨q, hq, he, hs, Z, i, j, hi, hfinite, hflat, hrank, hpull⟩

/-- FULL original Section5 lifting conclusion via LOCAL Hilbert universal
family. The actual characteristic prime remains a uniformizer, residue field
is exactly original k, and the special fibre is the SAME original point.
Every geometric lift is constructed; no Hilbert/lift outcome premise. -/
theorem exists_prime_uniformizer_smooth_cubic_lift_with_original_closed_subscheme_viaLocalHilbert317
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
  exact exists_smooth_lift_with_closed_subscheme_viaLocalHilbert317 b hb p hp hne x

/-- Literal paper-facing lemma: original field/cubic/closed point produce
characteristic-zero complete DVR, smooth lifted cubic, finiteflat rank d
closed family and EXACT original point special fibre, via LOCAL Hilbert. -/
theorem exists_smooth_charZero_cubic_lift_with_original_closed_subscheme_viaLocalHilbert317
    {k : Type u} [Field k]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : CharZero R)
      (b : R →+* k), Function.Surjective b ∧
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
  obtain ⟨R, _, _, _, _, _, b, hb, hmax, hker, hequiv, hfamily⟩ :=
    exists_prime_uniformizer_smooth_cubic_lift_with_original_closed_subscheme_viaLocalHilbert317
      ℓ hp hne x
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, hfamily⟩

end AllCharacteristics
end
