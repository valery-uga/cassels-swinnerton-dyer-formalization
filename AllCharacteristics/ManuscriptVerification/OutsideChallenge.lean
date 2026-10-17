import AllCharacteristics.InternalCorayPaperConclusions
import AllCharacteristics.OriginalGlobalHilbertChapterFiveIntegration
import AllCharacteristics.OriginalGlobalHilbertCubicSubschemeLifting
import AllCharacteristics.TwistedCubicLemma
import AllCharacteristics.TwoProofs
import AllCharacteristics.TwoProofsLiteralChaptersFiveSix
import AllCharacteristics.TwoProofsLiteralPreliminaries

/-! Explicit manuscript statement wrappers for Comparator.
Each comparator repeats the selected original type explicitly, as forall binders,
then proves it solely by @original. No existing theorem is renamed or replaced. -/

noncomputable section
namespace AllCharacteristics.PublicationComparators.OutsideSectionFour
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent IsLocalRing MvPolynomial Module
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option autoImplicit false
set_option linter.unusedVariables false

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:308; accepted 1736
theorem challenge_twoProofs_degree_four_closed_point_has_point :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:47; accepted 6412
theorem challenge_twoProofs_intro_finiteExtension_iff_internalCoray001 :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
  (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ↔
    (∃ (L : Type u) (hL : Field L),
      letI := hL
      ∃ hAlg : Algebra k L,
        letI := hAlg
        ∃ _ : Module.Finite k L,
          Nat.Coprime (Module.finrank k L) 3 ∧
          ∃ x : Fin 4 → L, x ≠ 0 ∧ p.eval₂ (algebraMap k L) x = 0) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:36; accepted 6412
theorem challenge_twoProofs_finite_point_coprime_has_point_internalCoray001 :
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0),
  ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:232; accepted 1736
theorem challenge_twoProofs_pfaffian_cubic_has_point :
  ∀ {k : Type u} [Field k] [NeZero (2 : k)]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (A : Fin 4 → Mat k 6) (hA : ∀ i, IsAlternating (A i))
    (hpresentation : (pfaffianCubic A).toMvPolynomial = p),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:166; accepted 1736
theorem challenge_twoProofs_secant :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 1 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 2),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofsLiteralPreliminaries.lean:19; accepted 1736
theorem challenge_twoProofs_position_perfect :
  ∀ {k : Type u} [Field k] [PerfectField k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5),
    let coplanar := ∃ c : Fin 4 → k, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (PfaffianDescent.homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal
    (coplanar → ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∧
    (¬ coplanar → PfaffianDescent.ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1)) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:71; accepted 1736
theorem challenge_twoProofs_twisted_cubic_smooth_embedding_of_algebraicClosure_presentation :
  ∀ {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i),
  QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwistedCubicLemma.lean:801; accepted 1736
theorem challenge_paper_twisted_cubic_perfect :
  ∀ {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i),
  QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ e : X ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:153; accepted 1736
theorem challenge_twoProofs_cassels_four_five :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)],
  (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ↔
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofsLiteralPreliminaries.lean:44; accepted 1736
theorem challenge_twoProofs_cassels_four_five_closed_point_alternative :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5),
  (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ y : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree y.1 =
        9 - (hypersurfaceToBase p hp).residueDegree x.1) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:297; accepted 1736
theorem challenge_twoProofs_degree_five_has_point :
  ∀ {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:140; accepted 1736
theorem challenge_twoProofs_incidence_finite_etale_degree_two_open :
  ∀ {k : Type u} [Field k] [NeZero (2 : k)],
  ∃ U : (alternatingTripleScheme k).Opens,
      (U : Set (alternatingTripleScheme k)).Nonempty ∧
      IsFinite (incidenceToTriples k ∣_ U) ∧ Etale (incidenceToTriples k ∣_ U) ∧
      ∀ x : U.toScheme, (incidenceToTriples k ∣_ U).finrank x = 2 :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:244; accepted 1736
theorem challenge_twoProofs_reduced_length_five_subscheme_pfaffian :
  ∀ {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hlen : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 5)
    (hposition : ProjectiveGeometricGeneralPosition (equationIdeal p hp) i),
  ∃ A : Fin 4 → Mat k 6, (∀ j, IsAlternating (A j)) ∧
      (pfaffianCubic A).toMvPolynomial = p :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:62; accepted 6412
theorem challenge_twoProofs_chapterFive_charzero_internalCoray001 :
  ∀ {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofsLiteralChaptersFiveSix.lean:304; accepted 1736
theorem challenge_twoProofs_chapterFive_lift :
  ChapterFiveLiftStatement.{u} :=
  by sorry

-- PfaffianDescent/AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean:18; accepted 6507
theorem challenge_chapterFiveLiftFor_viaGlobalHilbert001 :
  ∀ {k : Type u} [Field k],
  ChapterFiveLiftFor k :=
  by sorry

-- PfaffianDescent/AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean:27; accepted 6507
theorem challenge_chapterFiveLiftStatement_viaGlobalHilbert001 :
  ChapterFiveLiftStatement.{u} :=
  by sorry

-- PfaffianDescent/AllCharacteristics/OriginalGlobalHilbertCubicSubschemeLifting.lean:106; accepted 6505
theorem challenge_exists_smooth_charZero_cubic_lift_with_original_closed_subscheme_viaGlobalHilbert001 :
  ∀ {k : Type u} [Field k]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    {p : MvPolynomial (Fin 4) k} (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)),
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
            i (hypersurfaceReductionMap b q hq p hp he) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:74; accepted 6412
theorem challenge_twoProofs_chapterFive_smooth_internalCoray001 :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/OriginalGlobalHilbertChapterFiveIntegration.lean:35; accepted 6507
theorem challenge_twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001 :
  ∀ {k : Type u} [Field k] (ell : ℕ) [Fact ell.Prime] [CharP k ell]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (w : ZeroCycle (hypersurface p hp))
    (hw : ZeroCycle.degree (hypersurfaceToBase p hp) w = 1),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:86; accepted 6412
theorem challenge_twoProofs_chapterSix_main_internalCoray001 :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
  ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:25; accepted 6412
theorem challenge_twoProofs_main_theorem_internalCoray001 :
  ∀ {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
  (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofsLiteralChaptersFiveSix.lean:511; accepted 1736
theorem challenge_twoProofs_chapterSix_singular_point_scheme :
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (a : Spec (.of L) ⟶ hypersurface (p.map (algebraMap k L))
      (hp.map (algebraMap k L)))
    (ha : a ≫ hypersurfaceToBase (p.map (algebraMap k L))
      (hp.map (algebraMap k L)) = 𝟙 _),
  (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      ∃ q : Spec (.of L) ⟶ hypersurface (p.map (algebraMap k L))
        (hp.map (algebraMap k L)),
        q ≫ hypersurfaceToBase (p.map (algebraMap k L))
          (hp.map (algebraMap k L)) = 𝟙 _ ∧
        q (IsLocalRing.closedPoint L) ∈
          (hypersurfaceToBase (p.map (algebraMap k L))
            (hp.map (algebraMap k L))).smoothLocus :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofs.lean:329; accepted 1736
theorem challenge_twoProofs_singular_point_or_smooth_extension_point :
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0),
  (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ∨
      ∃ q : Fin 4 → L,
        IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) q :=
  by sorry

-- PfaffianDescent/AllCharacteristics/TwoProofsLiteralChaptersFiveSix.lean:570; accepted 1736
theorem challenge_twoProofs_chapterSix_smoothing :
  ∀ {k : Type u} [Field k]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (FractionRing (PowerSeries k)))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1),
  ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  by sorry

-- PfaffianDescent/AllCharacteristics/InternalCorayPaperConclusions.lean:18; accepted 6412
theorem challenge_internalCorayDegreeOneFourOrTenFor_uniform001 :
  ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K :=
  by sorry

end AllCharacteristics.PublicationComparators.OutsideSectionFour
end
