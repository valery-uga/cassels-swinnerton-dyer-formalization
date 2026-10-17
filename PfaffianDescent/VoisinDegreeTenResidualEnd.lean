import PfaffianDescent.VoisinFiniteSubschemeDatumResidual
import PfaffianDescent.VoisinFiniteSubschemeRankTwoFamily
import PfaffianDescent.NormalizedTripleCompleteIntersection
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.ProjectiveIdealCancellation
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# The finite-subscheme end of Voisin's degree-ten reduction

The middle rank-two geometry supplies a degree-three closed component in a
finite étale degree-eleven scheme. Its annihilator residual has degree eight,
and the final cubic--quadric--quadric residual then supplies degree four.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Algebraic form of Voisin's assertion that the quadratic system through a
rank-eight datum has no fixed curve component. -/
def DegreeEightQuadraticSystemHasNoCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
    q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
    q ≠ 0 ∧ IsRelPrime p q ∧
    let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
    let W := homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
        (MvPolynomial (Fin 4) K ⧸ I),
      ∃ r ∈ W, Ideal.Quotient.mk I r ∉ P

/-- The literal proper-intersection conclusion supplied by the final
quadratic Bertini step. -/
def DegreeEightRegularQuadricPairExists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
    q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
    q ≠ 0 ∧ IsRelPrime p q ∧
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
      r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))

/-- Associated-prime avoidance selects a regular second quadric. -/
theorem DegreeEightQuadraticSystemHasNoCommonCurveComponent.regularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hnofixed : DegreeEightQuadraticSystemHasNoCommonCurveComponent p hp D₈) :
    DegreeEightRegularQuadricPairExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx
  obtain ⟨q, hq, hqvan, hq0, hrel, havoid⟩ := hnofixed x hx
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_avoids_associatedPrimes p q x havoid
  exact ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hregular⟩

/-- The rank-eight residual of the finite étale rank-eleven stage has all
the data needed for the first quadric in Voisin's final residual whenever the
cubic surface is prime. Hence the only section-selection condition left in
the `8 → 4` step is primeness of the selected cubic--quadric intermediate
curve. -/
theorem exists_rankEightResidual_regular_quadric_section_of_prime_surface
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3) :
    let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c
      (hypersurfaceToBase p hp) hW hZ
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q := by
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c
    (hypersurfaceToBase p hp) hW hZ
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  exact cubicFiniteSubscheme_degree_eight_regular_quadric_section_of_prime_surface
    p hp hne D.val.subschemeι
    (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
      (hypersurfaceToBase p hp) D)
    hprime

/-- Smoothness supplies the primeness used to choose the first quadric in
the final residual.  Thus the `11 → 8 → 4` stage has no independent
surface-integrality premise: after the rank-three component is provided by
the rank-two construction, only the selected quadratic intermediate and its
transverse final quadric remain geometric choices. -/
theorem exists_rankEightResidual_regular_quadric_section_of_smooth_cubic
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3) :
    let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c
      (hypersurfaceToBase p hp) hW hZ
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q := by
  apply exists_rankEightResidual_regular_quadric_section_of_prime_surface
    p hp hne
  exact principalIdeal_prime_of_irreducible_cubic p
    (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)

/-- A specified transverse cubic--quadric--quadric intersection through the
rank-eight residual of a rank-eleven finite étale scheme produces Voisin's
finite étale rank-four residual.  This is the direct final-residual interface,
with no selected-prime or uniform-transversality strengthening. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (coordinates : let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c (hypersurfaceToBase p hp) hW hZ
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (htransverse : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c
    (hypersurfaceToBase p hp) hW hZ
  let _ : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  let _ : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := htransverse
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D coordinates
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D coordinates

/-- Associated-component avoidance for a chosen cubic--quadric curve selects
the final quadric through the rank-eight residual.  Thus the final Voisin
residual does not require the intermediate curve to be prime; it requires
only the exact avoidance condition used by the regular-section argument and
transversality for the resulting complete intersection. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_avoids_associatedPrimes
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (coordinates : let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c (hypersurfaceToBase p hp) hW hZ
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 2,
            Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r ∉ P))
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 2),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c
    (hypersurfaceToBase p hp) hW hZ
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, havoid⟩ := coordinates
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_avoids_associatedPrimes p q x havoid
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
    htransverse r hr hregular
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- The numerical base-locus formulation of the final residual.  A
rank-drop estimate for the quadratic system through the rank-eight residual
selects the final quadric, so the rank-two stage only has to supply that
estimate and transversality of the selected complete intersection. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_finrank_drop
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (coordinates : let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c (hypersurfaceToBase p hp) hW hZ
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hdrop : let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c (hypersurfaceToBase p hp) hW hZ
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
        let W := homogeneousVanishingPolynomialSubmodule
          (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 2
        let qmap : MvPolynomial (Fin 4) K →ₗ[K]
            MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
        let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
        ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
            (MvPolynomial (Fin 4) K ⧸ I),
          Module.finrank K ((P.restrictScalars K).comap V.subtype) <
            Module.finrank K V)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 2),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_finiteSubschemeDatum_degree_eight_residual_and_toBase_etale_of_selected_finrank_drop
      p q hp hq hne hrel
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ)
      coordinates hdrop htransverse

/-- The point-specific final Bertini step after the rank-eleven residual. A
single chosen regular transverse quadric through its rank-eight residual gives
the degree-four datum; no universal transversality statement is required. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_regular_transverse_quadric
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (selected : let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c (hypersurfaceToBase p hp) hW hZ
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell r : MvPolynomial (Fin 4) K)
        (hr : r.IsHomogeneous 2),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_finiteSubschemeDatum_degree_eight_residual_and_toBase_etale_of_selected_regular_transverse_quadric
      p q hp hq hne hrel
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ)
      selected

/-- The concrete output required from the final Bertini step, stated directly
for the rank-eight datum produced by the rank-two construction.  This does
not require that datum to be a closed component of the preceding rank-eleven
residual: Proposition 3.2 relates the two cycles through a pencil. -/
structure DegreeEightTransverseQuadricIntersectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) where
  q : MvPolynomial (Fin 4) K
  r : MvPolynomial (Fin 4) K
  hq : q.IsHomogeneous 2
  hr : r.IsHomogeneous 2
  hrel : IsRelPrime p q
  coordinates :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI := finiteSchemeCoefficientAlgebra (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0
  regular : ∀ y : MvPolynomial (Fin 4) K,
    r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
      y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  transverse : Etale
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- The final transverse intersection together with the actual embedding of
the rank-eight endpoint.  This containment is the scheme-theoretic datum
that makes the degree-four scheme a residual of the endpoint supplied by the
rank-two pencil, rather than merely another degree-four scheme of the same
numerical rank. -/
structure DegreeEightTransverseQuadricIntersectionEmbeddingData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) where
  q : MvPolynomial (Fin 4) K
  r : MvPolynomial (Fin 4) K
  hq : q.IsHomogeneous 2
  hr : r.IsHomogeneous 2
  hrel : IsRelPrime p q
  regular : ∀ y : MvPolynomial (Fin 4) K,
    r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
      y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  embedding : D₈.val.subscheme ⟶
    scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)
  embedding_closed : IsClosedImmersion embedding
  embedding_over : embedding ≫
      tripleCompleteIntersectionToHypersurface p q r hp hq hr =
    D₈.val.subschemeι
  transverse : Etale
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- Build the final embedded-intersection datum from an isomorphic
presentation of the rank-eight endpoint.  The hypothesis records equality
over the cubic surface, so the transported map is a genuine containment of
the endpoint used by the final pencil. -/
noncomputable def DegreeEightTransverseQuadricIntersectionEmbeddingData.ofPresentation
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (e : Z ≅ D₈.val.subscheme)
    (j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      e.hom ≫ D₈.val.subschemeι)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈ :=
  { q := q
    r := r
    hq := hq
    hr := hr
    hrel := hrel
    regular := hregular
    embedding := finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso
      p q r hp hq hr 8 D₈ e j
    embedding_closed := by infer_instance
    embedding_over := finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso_fac
      p q r hp hq hr 8 D₈ e j hj
    transverse := htransverse }

/-- The final endpoint can likewise be supplied by the intrinsic ideal-sheaf
containment of the cubic--quadric--quadric intersection in the rank-eight
subscheme. -/
noncomputable def DegreeEightTransverseQuadricIntersectionEmbeddingData.ofKernelLe
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hker : (tripleCompleteIntersectionToHypersurface p q r hp hq hr).ker ≤
      D₈.val.subschemeι.ker)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈ :=
  { q := q
    r := r
    hq := hq
    hr := hr
    hrel := hrel
    regular := hregular
    embedding := tripleCompleteIntersectionLift
      p q r hp hq hr D₈.val.subschemeι hker
    embedding_closed := by infer_instance
    embedding_over := tripleCompleteIntersectionLift_fac
      p q r hp hq hr D₈.val.subschemeι hker
    transverse := htransverse }

/-- Construct the final embedded cubic--quadric--quadric intersection from
the normalized chart of the actual rank-eight endpoint.  Vanishing of the
two quadrics on this chart yields equality with the given endpoint immersion
over the cubic surface. -/
noncomputable def DegreeEightTransverseQuadricIntersectionEmbeddingData.ofNormalizedChart
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (chart : letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI : IsAffine D₈.val.subscheme :=
        isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (z : CoordinateRing (equationIdeal p hp))
        (hz : z ∈ grading (equationIdeal p hp) 1)
        (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
        (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
          (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
        (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
          (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈ := by
  exact
    { q := q
      r := r
      hq := hq
      hr := hr
      hrel := hrel
      regular := hregular
      embedding := finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
        p q r hp hq hr 8 D₈ chart
      embedding_closed :=
        finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_isClosedImmersion
          p q r hp hq hr 8 D₈ chart
      embedding_over :=
        finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_fac
          p q r hp hq hr 8 D₈ chart
      transverse := htransverse }

/-- The actual degree-four residual defined from the final embedded
cubic--quadric--quadric intersection. -/
noncomputable def degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (T : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 4 := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular D₈ T.embedding T.embedding_over

/-- The final embedded residual has degree four. -/
theorem degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_cycle_degree
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (T : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈) :
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp)
        (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
          p hp hne D₈ T)) = 4 :=
  finiteSubschemeDatumCycle_degree _ _

/-- The final embedded residual is finite étale over the ground field. -/
theorem degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_toBase_etale
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (T : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈) :
    Etale
      ((degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
        p hp hne D₈ T).val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_toBase_etale
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular D₈ T.embedding T.embedding_over

/-- The final embedded residual is disjoint from the rank-eight datum to
which the two quadrics were applied. -/
theorem degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (T : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈) :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
          p hp hne D₈ T))) := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact (disjoint_finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular D₈ T.embedding T.embedding_over).symm

/-- The finite-rank form of the final base-locus condition in Voisin's
degree-ten argument.  It concerns the second quadric through the rank-eight
residual, after every admissible first quadric has been selected. -/
def DegreeEightSecondQuadricFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∀ (q : MvPolynomial (Fin 4) K),
  q.IsHomogeneous 2 →
  q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
  q ≠ 0 → IsRelPrime p q →
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
  let qmap : MvPolynomial (Fin 4) K →ₗ[K]
      MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    Module.finrank K ((P.restrictScalars K).comap V.subtype) <
      Module.finrank K V

/-- The algebraic property of the finite complete intersections used by
Voisin's proper-intersection proof.  A regular cubic--quadric--quadric
complete intersection is zero-dimensional of length twelve; this predicate
records that its coordinate algebra is Frobenius.  Unlike transversality, it
allows nonreduced intersections. -/
def CubicTwoQuadricRegularCompleteIntersectionsFrobenius
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
    letI := cubic_two_quadrics_intersection_finite
      p q r hp hq hr hne hq0 hrel hregular
    letI := finiteSchemeCoefficientAlgebra
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    ∃ ell : Module.Dual K
        Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
      IsFrobeniusFunctional ell
/-- The geometric form of the same final base-locus condition: the remaining
quadric system is not contained in any associated component of the selected
cubic--quadric curve. -/
def DegreeEightSecondQuadricAvoidsAssociatedPrimes
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∀ (q : MvPolynomial (Fin 4) K),
  q.IsHomogeneous 2 →
  q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
  q ≠ 0 → IsRelPrime p q →
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    ∃ r ∈ W, Ideal.Quotient.mk I r ∉ P

/-- Associated-component avoidance gives the finite-rank form used to choose
the final regular quadric. -/
theorem DegreeEightSecondQuadricAvoidsAssociatedPrimes.finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈) :
    DegreeEightSecondQuadricFinrankDrop p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q hq hqvan hq0 hrel
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2)).mp
    (havoid x hx q hq hqvan hq0 hrel)

/-- The finite-rank packaging loses no geometric information: it recovers
associated-component avoidance for every admissible first quadric. -/
theorem DegreeEightSecondQuadricAvoidsAssociatedPrimes.ofFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdrop : DegreeEightSecondQuadricFinrankDrop p hp D₈) :
    DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q hq hqvan hq0 hrel
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2)).mpr
    (hdrop x hx q hq hqvan hq0 hrel)

/-- The two formulations of the final base-locus condition are equivalent. -/
theorem degreeEightSecondQuadric_avoidsAssociatedPrimes_iff_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) :
    DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈ ↔
      DegreeEightSecondQuadricFinrankDrop p hp D₈ := by
  constructor
  · exact DegreeEightSecondQuadricAvoidsAssociatedPrimes.finrankDrop p hp D₈
  · exact DegreeEightSecondQuadricAvoidsAssociatedPrimes.ofFinrankDrop p hp D₈

/- The final Bertini/transversality premise is also expressible directly on
   normalized charts.  This is the cubic--quadric--quadric analogue of the
   first-residual Jacobian interface in `VoisinDegreeTenSmoothStart`. -/
def CubicTwoQuadricIntersectionChartJacobianUnit
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
    q ≠ 0 → IsRelPrime p q →
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
    ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)

theorem CubicTwoQuadricIntersectionChartJacobianUnit.toTransverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hjac : CubicTwoQuadricIntersectionChartJacobianUnit p hp) :
    ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  intro q r hq hr hq0 hrel hregular
  exact etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    p q r hp hq hr (hjac q r hq hr hq0 hrel hregular)

/-- The exact simultaneous conclusion needed from the last section-selection
step.  After an admissible first quadric through the rank-eight datum has been
chosen, one asks for a single second quadric in the same vanishing system
which is both regular on the cubic--quadric curve and transverse there.  This
avoids the stronger, unnecessary assertion that every regular second quadric
is transverse. -/
def DegreeEightRegularTransverseSecondQuadricExists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
  q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
  q ≠ 0 → IsRelPrime p q →
  ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
    r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- Separate associated-prime avoidance and Bertini hypotheses imply the
point-specific simultaneous selector.  This records that the older universal
transversality interface is sufficient, while the selector itself asks for
only the one member used by the residual construction. -/
theorem DegreeEightRegularTransverseSecondQuadricExists.ofFinrankDrop_and_transverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdrop : DegreeEightSecondQuadricFinrankDrop p hp D₈)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    DegreeEightRegularTransverseSecondQuadricExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q hq hqvan hq0 hrel
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_finrank_drop p q x
      (hdrop x hx q hq hqvan hq0 hrel)
  exact ⟨r, hr, hrvan, hregular,
    htransverse q r hq hr hq0 hrel hregular⟩

/-- The geometric associated-component condition together with the
chart-Jacobian Bertini condition supplies the exact simultaneous selector. -/
theorem DegreeEightRegularTransverseSecondQuadricExists.ofAvoidance_and_chartJacobian
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈)
    (hjac : CubicTwoQuadricIntersectionChartJacobianUnit p hp) :
    DegreeEightRegularTransverseSecondQuadricExists p hp D₈ :=
  .ofFinrankDrop_and_transverse p hp D₈
    (havoid.finrankDrop p hp D₈) (hjac.toTransverse p hp)
/-- On a smooth cubic, a rank-eight finite datum has a first regular quadric
section and a normalized chart retaining its actual immersion.  Thus the
last associated-prime rank-drop and transverse-intersection inputs construct
the degree-four residual as a scheme disjoint from that exact rank-eight
datum, rather than only as a cycle of the right degree. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdrop :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      q.IsHomogeneous 2 →
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
      q ≠ 0 → IsRelPrime p q →
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
      let qmap : MvPolynomial (Fin 4) K →ₗ[K]
          MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_chart p hp D₈.val.subschemeι
  have hsections : 2 ≤ Module.finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) :=
    quadric_degree_eight_vanishing_sections_finrank x
      ((finiteSchemeCoefficient_finrank
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
        (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
          (hypersurfaceToBase p hp) D₈))
  obtain ⟨q, hq, hqvan, hq0, hrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp
      ((Ideal.span_singleton_prime hne).mp hprime) x hsections
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_second_quadric_data_of_finrank_drop p q x
      (hdrop x hxsurj q hq hqvan hq0 hrel)
  let T := DegreeEightTransverseQuadricIntersectionEmbeddingData.ofNormalizedChart
    p q r hp hq hr D₈ hrel hregular
    ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
    (htransverse q r hq hr hq0 hrel hregular)
  refine ⟨degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
    p hp hne D₈ T, ?_, ?_, ?_⟩
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_cycle_degree
      p hp hne D₈ T
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_toBase_etale
      p hp hne D₈ T
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
      p hp hne D₈ T

/-- The final degree-eight residual construction from the point-specific
simultaneous selector.  The proof chooses the first regular quadric, invokes
the selector once for that quadric, and retains the actual embedding of the
rank-eight datum in the resulting complete intersection. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_regularTransverseSecondQuadric
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hselect : DegreeEightRegularTransverseSecondQuadricExists p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_chart p hp D₈.val.subschemeι
  have hsections : 2 ≤ Module.finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) :=
    quadric_degree_eight_vanishing_sections_finrank x
      ((finiteSchemeCoefficient_finrank
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
        (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
          (hypersurfaceToBase p hp) D₈))
  obtain ⟨q, hq, hqvan, hq0, hrel⟩ :=
    exists_quadric_section_data_isRelPrime_of_prime_cubic p hp
      ((Ideal.span_singleton_prime hne).mp hprime) x hsections
  obtain ⟨r, hr, hrvan, hregular, htransverse⟩ :=
    hselect x hxsurj q hq hqvan hq0 hrel
  let T := DegreeEightTransverseQuadricIntersectionEmbeddingData.ofNormalizedChart
    p q r hp hq hr D₈ hrel hregular
    ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩ htransverse
  refine ⟨degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
    p hp hne D₈ T, ?_, ?_, ?_⟩
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_cycle_degree
      p hp hne D₈ T
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_toBase_etale
      p hp hne D₈ T
  · exact degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
      p hp hne D₈ T
/-- The final base-locus hypothesis in Voisin's construction has a direct
geometric form: after every admissible first quadric through the rank-eight
datum, the remaining quadrics are not all contained in any associated
component of the cubic--quadric curve.  This is equivalent to the
finite-rank condition consumed by the regular-section construction. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_avoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid :
      letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
      letI := finiteSchemeCoefficientAlgebra
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∀ (x : Fin 4 → Γ(D₈.val.subscheme, ⊤)),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
      ∀ (q : MvPolynomial (Fin 4) K),
      q.IsHomogeneous 2 →
      q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 →
      q ≠ 0 → IsRelPrime p q →
      let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
      let W := homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
          (MvPolynomial (Fin 4) K ⧸ I),
        ∃ r ∈ W, Ideal.Quotient.mk I r ∉ P)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  apply exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
    p hp hne D₈ ?_ htransverse
  intro x hx q hq hqvan hq0 hrel
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2)).mp
    (havoid x hx q hq hqvan hq0 hrel)

/-- A named version of the final associated-component hypothesis in Voisin's
degree-ten construction.  It packages the geometric condition independently
of the finite-dimensional linear-algebra implementation. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_secondQuadricAvoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_avoidsAssociatedPrimes
    p hp hne D₈ havoid htransverse

/- The final residual can therefore be driven by an explicit chartwise
   Jacobian calculation, with the associated-component condition kept in its
   geometric form. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_secondQuadricAvoidsAssociatedPrimes_of_chartJacobianUnit
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (havoid : DegreeEightSecondQuadricAvoidsAssociatedPrimes p hp D₈)
    (hjac : CubicTwoQuadricIntersectionChartJacobianUnit p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_secondQuadricAvoidsAssociatedPrimes
    (K := K) p hp hne D₈ havoid
    (CubicTwoQuadricIntersectionChartJacobianUnit.toTransverse p hp hjac)

/-- A concrete transverse cubic--quadric--quadric datum through an arbitrary
rank-eight finite datum produces the finite étale degree-four residual. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_of_transverseQuadricIntersectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (T : DegreeEightTransverseQuadricIntersectionData p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩ := T.coordinates
  exact
    exists_finiteSubschemeDatum_degree_eight_residual_and_toBase_etale_of_selected_regular_transverse_quadric
      p T.q hp T.hq hne T.hrel D₈
      ⟨x, ell, T.r, T.hr, hxsurj, hell, hxell, hpx, hqvan, hrvan,
        T.regular, T.transverse⟩

/-- The correctly independent residual spine in Voisin's degree-ten proof.
The first transverse cubic data gives the rank-eleven residual.  Proposition
3.2 then supplies a finite-flat pencil from it to the union of a degree-three
reference datum and a rank-eight datum; the final transverse quadrics apply
to that rank-eight endpoint.  In particular, no artificial degree-three
component of the original rank-eleven residual is assumed. -/
theorem exists_degreeFourResidualDatum_and_rankTwoFamily_of_selected_rankTwoData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T₁₆ : DegreeTenTransverseCubicIntersectionData p hp D₁₀)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdisjoint : Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (P : FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 11
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ hdisjoint)
      (degreeTenResidualDatumOfTransverseCubicIntersectionData p hp hne D₁₀ T₁₆))
    (T₈ : DegreeEightTransverseQuadricIntersectionData p hp D₈) :
    ∃ R₄ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R₄) = 4 ∧
      Etale (R₄.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      ∃ F : RationalCycleFamily (hypersurfaceToBase p hp),
        F.fiberCycle false =
          finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃ +
            finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₈ ∧
        F.fiberCycle true = finiteSubschemeDatumCycle (hypersurfaceToBase p hp)
          (degreeTenResidualDatumOfTransverseCubicIntersectionData p hp hne D₁₀ T₁₆) := by
  obtain ⟨R₄, hdegree, hetale⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_of_transverseQuadricIntersectionData
      p hp hne D₈ T₈
  refine ⟨R₄, hdegree, hetale, ?_⟩
  exact exists_rankTwoResidualFamily_of_pencil (hypersurfaceToBase p hp)
    D₈ D₃
    (degreeTenResidualDatumOfTransverseCubicIntersectionData p hp hne D₁₀ T₁₆)
    hdisjoint P

/-- The last two residual ranks use Frobenius functionals rather than
étaleness: a rank-three component of a Frobenius rank-eleven scheme has a
finite-flat rank-eight residual, and a Frobenius cubic--quadric--quadric
intersection then has a finite-flat rank-four residual. -/
theorem exists_degreeFourResidualDatum_of_rankElevenFrobeniusComponent_and_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (hWfrob :
      letI := finiteSchemeCoefficientAlgebra
        (c ≫ hypersurfaceToBase p hp)
      ∃ ell : Module.Dual K Γ(W, ⊤), IsFrobeniusFunctional ell)
    (coordinates :
      let D := finiteSubschemeDatumRankEightOfRankElevenResidual (K := K) (X := W) (Y := hypersurface p hp) (Z := Z)
        i c (hypersurfaceToBase p hp) hW hZ hWfrob
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne
          (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel)
          hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 := by
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  let D := finiteSubschemeDatumRankEightOfRankElevenResidual
    (K := K) (X := W) (Y := hypersurface p hp) (Z := Z)
    i c (hypersurfaceToBase p hp) hW hZ hWfrob
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  let R := finiteSubschemeDatum_degree_eight_residual_of_selected_coordinates_of_frobenius
    p q r hp hq hr hne hq0 hrel hregular D coordinates hfrob
  exact ⟨R, finiteSubschemeDatumCycle_degree _ _⟩

/-- The final residual can be stated directly from containment of the
rank-eight residual subscheme in the selected cubic--quadric--quadric
intersection.  This is the scheme-level form of the final choice in
Voisin's construction, and removes the incidental normalized-coordinate
presentation from this interface. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (j : (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
      i c (hypersurfaceToBase p hp) hW hZ).val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ).val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    i c (hypersurfaceToBase p hp) hW hZ
  let R := finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular D j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D j hj

/-- The rank-four datum from the final transverse complete intersection is
automatically disjoint from the rank-eight residual to which the quadrics
were applied.  Hence the final pencil's support condition is supplied by the
residual construction, leaving only the geometric construction of that
pencil itself. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_rankElevenEtaleComponent_and_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (j : (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
      i c (hypersurfaceToBase p hp) hW hZ).val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ).val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
            i c (hypersurfaceToBase p hp) hW hZ)))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    i c (hypersurfaceToBase p hp) hW hZ
  let R := finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular D j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_, ?_⟩
  · exact finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_toBase_etale
      p q r hp hq hr hne hq0 hrel hregular D j hj
  · exact (disjoint_finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular D j hj).symm

/-- Reducedness of the final regular cubic--quadric--quadric intersection
supplies its finite étaleness in characteristic zero.  The rank-four residual
and its support separation therefore need no additional étaleness premise. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_rankElevenEtaleComponent_and_reduced_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (j : (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
      i c (hypersurfaceToBase p hp) hW hZ).val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ).val.subschemeι)
    [AlgebraicGeometry.IsReduced (scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
            i c (hypersurfaceToBase p hp) hW hZ)))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  letI : IsFinite (toBase I) := cubic_two_quadrics_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : Etale (toBase I) := finiteScheme_etale_of_isReduced (toBase I)
  exact
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_rankElevenEtaleComponent_and_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular i c hW hZ j hj

/-- The final embedded-intersection construction likewise has a Frobenius
form.  It produces the finite-flat degree-four residual before imposing the
étaleness used by later geometric arguments. -/
theorem exists_degreeFourResidualDatum_of_rankElevenFrobeniusComponent_and_completeIntersectionEmbedding_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (hWfrob :
      letI := finiteSchemeCoefficientAlgebra
        (c ≫ hypersurfaceToBase p hp)
      ∃ ell : Module.Dual K Γ(W, ⊤), IsFrobeniusFunctional ell)
    (j : (finiteSubschemeDatumRankEightOfRankElevenResidual
      (K := K) (X := W) (Y := hypersurface p hp) (Z := Z)
      i c (hypersurfaceToBase p hp) hW hZ hWfrob).val.subscheme ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (finiteSubschemeDatumRankEightOfRankElevenResidual
        (K := K) (X := W) (Y := hypersurface p hp) (Z := Z)
        i c (hypersurfaceToBase p hp) hW hZ hWfrob).val.subschemeι)
    (hfrob :
      letI := cubic_two_quadrics_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 := by
  let D := finiteSubschemeDatumRankEightOfRankElevenResidual
    (K := K) (X := W) (Y := hypersurface p hp) (Z := Z)
    i c (hypersurfaceToBase p hp) hW hZ hWfrob
  let R :=
    finiteSubschemeDatum_degree_eight_residual_of_completeIntersectionEmbedding_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular D j hj hfrob
  exact ⟨R, finiteSubschemeDatumCycle_degree _ _⟩

/-- The finite-scheme part of Voisin's last two steps. A degree-three closed
component in the finite étale degree-eleven ambient scheme yields the actual
rank-eight residual datum. Once the selected quadrics contain that datum and
form a transverse complete intersection, their residual is an actual rank-four
datum on the original cubic surface. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (hselected : let D := (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ)
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_finiteSubschemeDatum_degree_eight_residual_of_selected_prime_intermediate
    p hp hne
    (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
      i c (hypersurfaceToBase p hp) hW hZ)
    hselected htransverse

/-- The final quadratic residual accepts the intrinsic Bertini conclusion
that the selected quadric is prime in the cubic-surface coordinate ring. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_quotientPrime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hselected : let D := (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ)
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        Prime (Ideal.Quotient.mk
          (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) q))
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    i c (hypersurfaceToBase p hp) hW hZ
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨a, ell, q, ha, hell, hellone, hpvan, hq, hqvan, hq0, hrel, hqprime⟩ :=
    hselected
  exact exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_prime_intermediate
    p hp hne i c hW hZ
    ⟨a, ell, q, ha, hell, hellone, hpvan, hq, hqvan, hq0, hrel,
      ideal_span_pair_isPrime_of_quotient_mk_prime p q hpprime hqprime⟩
    htransverse

/-- On a smooth cubic, the surface equation is prime automatically, so the
intrinsic selected-quadric condition is the only primeness input in the
final residual construction. -/
theorem exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_quotientPrime_intermediate_of_smooth_cubic
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3)
    (hselected : let D := (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
        i c (hypersurfaceToBase p hp) hW hZ)
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.IsHomogeneous 2 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        Prime (Ideal.Quotient.mk
          (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) q))
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_quotientPrime_intermediate
      p hp hne i c hW hZ
      (principalIdeal_prime_of_irreducible_cubic p
        (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne))
      hselected htransverse

/-- A special componentwise residual construction.  If a degree-three closed
component already lies in the selected rank-eleven scheme, its complementary
rank-eight residual can be used directly for the final quadratic step.

This is stronger than the general situation in Voisin's Proposition 3.2,
where the rank-eight datum is related to the rank-eleven datum by a moving
pencil.  The general interface is
`exists_degreeFourResidualDatum_and_rankTwoFamily_of_selected_rankTwoData`. -/
theorem exists_degreeEleven_and_degreeFour_residualData_of_selected_geometric_data
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp D₁₀)
    (hcomponentAndFinal :
      ∀ (R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
        [IsFinite (R.val.subschemeι ≫ hypersurfaceToBase p hp)]
        [Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp)]
        (hR : finiteSchemeRank (R.val.subschemeι ≫ hypersurfaceToBase p hp) = 11),
        ∃ (Z : Scheme.{u}) (i : Z ⟶ R.val.subscheme) (hi : IsClosedImmersion i),
          letI : IsClosedImmersion i := hi
          ∃
          (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2)
          (hrel : IsRelPrime p q)
          (hZ : finiteSchemeRank
            (i ≫ R.val.subschemeι ≫ hypersurfaceToBase p hp) = 3),
          let D := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
            i R.val.subschemeι (hypersurfaceToBase p hp) hR hZ
          letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
          letI := finiteSchemeCoefficientAlgebra
            (D.val.subschemeι ≫ hypersurfaceToBase p hp)
          ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
            (ell r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
            Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
            ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
            p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
            q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
            r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
            (∀ y : MvPolynomial (Fin 4) K,
              r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
                y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
            Etale (toBase
              (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R₁₁) = 11 ∧
      Etale (R₁₁.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      ∃ R₄ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
            (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R₄) = 4 ∧
        Etale (R₄.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  obtain ⟨R₁₁, hdeg₁₁, hEtale₁₁⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      p hp hne D₁₀ T
  letI : IsFinite (R₁₁.val.subschemeι ≫ hypersurfaceToBase p hp) := R₁₁.property.1
  have hrank₁₁ : finiteSchemeRank
      (R₁₁.val.subschemeι ≫ hypersurfaceToBase p hp) = 11 := by
    rw [finiteSchemeRank_eq_finrank]
    exact R₁₁.property.2.2.2 (IsLocalRing.closedPoint K)
  letI : Etale (R₁₁.val.subschemeι ≫ hypersurfaceToBase p hp) := hEtale₁₁
  obtain ⟨Z, i, hi, q, hq, hrel, hZ, hselected⟩ :=
    hcomponentAndFinal R₁₁ hrank₁₁
  letI : IsClosedImmersion i := hi
  obtain ⟨R₄, hdeg₄, hEtale₄⟩ :=
    exists_degreeFourResidualDatum_of_rankElevenEtaleComponent_and_selected_regular_transverse_quadric
      p q hp hq hne hrel i R₁₁.val.subschemeι hrank₁₁ hZ hselected
  exact ⟨R₁₁, hdeg₁₁, hEtale₁₁, R₄, hdeg₄, hEtale₄⟩

/-- The complete scheme-level three-pencil package from actual embedded
residual data.  The first and last support-separation fields are derived
from their transverse complete intersections.  Consequently the remaining
geometric input is exactly the construction of the three pencils, the
rank-eight-plus-rank-three middle endpoint, and their reference-cycle
identifications. -/
noncomputable def voisinDegreeTenPointPencilData_of_embeddedResidualData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T₁₆ : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀)
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (P₁₆ : let hdisjoint :=
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
        p hp hne D₁₀ T₁₆)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 27
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          T₁₆.completion.datum
          (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
            p hp hne D₁₀ T₁₆) hdisjoint) D₂₇)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (P₁₁ : FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 11
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃)
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
        p hp hne D₁₀ T₁₆))
    (T₈ : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈)
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (P₈ : let hdisjoint :=
      (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
        p hp hne D₈ T₈)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 12
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp) D₈
          (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
            p hp hne D₈ T₈) hdisjoint) D₁₂) :
    VoisinDegreeTenPointPencilData (hypersurfaceToBase p hp) := by
  let h₁₆₁₁ :=
    degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
      p hp hne D₁₀ T₁₆
  let h₈₄ :=
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
      p hp hne D₈ T₈
  exact
    { D₁₆ := T₁₆.completion.datum
      D₁₁ := degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
        p hp hne D₁₀ T₁₆
      disjoint₁₆₁₁ := h₁₆₁₁
      D₂₇ := D₂₇
      cubicPencil := P₁₆
      D₃ := D₃
      D₈ := D₈
      disjoint₈₃ := h₈₃
      rankTwoPencil := P₁₁
      D₄ := degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
        p hp hne D₈ T₈
      disjoint₈₄ := h₈₄
      D₁₂ := D₁₂
      quadricPencil := P₈ }

/-- The actual embedded complete intersections and three finite-flat pencils
give Voisin's point-specific degree-ten steps once their endpoint classes are
identified.  The first and last disjointness conditions are derived from the
embedded residual constructions, so no separate support hypotheses remain in
this formulation. -/
theorem voisinDegreeTenPointSteps_of_embeddedResidualData_and_cycleClasses
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (T₁₆ : DegreeTenTransverseCubicIntersectionEmbeddingData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (P₁₆ : let hdisjoint :=
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
        p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 27
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          T₁₆.completion.datum
          (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
            (finiteSubschemeDatumOfClosedPointOfResidueDegree
              (hypersurfaceToBase p hp) x 10 hx) T₁₆) hdisjoint) D₂₇)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (P₁₁ : FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 11
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃)
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆))
    (T₈ : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈)
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (P₈ : let hdisjoint :=
      (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
        p hp hne D₈ T₈)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 12
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp) D₈
          (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
            p hp hne D₈ T₈) hdisjoint) D₁₂)
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  let S := voisinDegreeTenPointPencilData_of_embeddedResidualData p hp hne
    (finiteSubschemeDatumOfClosedPointOfResidueDegree
      (hypersurfaceToBase p hp) x 10 hx)
    T₁₆ D₂₇ P₁₆ D₃ D₈ h₈₃ P₁₁ T₈ D₁₂ P₈
  exact voisinDegreeTenPointSteps_of_completion_and_cycleClasses p hp x hx T₁₆.completion h
    hfirst hsecond S rfl cycle₂₇ cycle₃ cycle₁₂

/- The middle rank-two pencil may be supplied directly by the Serre gluing
   construction.  Its literal endpoints are allowed to be identified with
   the degree-eight-plus-degree-three datum and the degree-eleven residual by
   isomorphisms over the cubic surface; the retargeting theorem then supplies
   the abstract pencil required by the point-specific Voisin argument. -/
theorem voisinDegreeTenPointSteps_of_embeddedResidualData_and_projectiveLinePencil
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (T₁₆ : DegreeTenTransverseCubicIntersectionEmbeddingData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (P₁₆ : let hdisjoint :=
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
        p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 27
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          T₁₆.completion.datum
          (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
            p hp hne
            (finiteSubschemeDatumOfClosedPointOfResidueDegree
              (hypersurfaceToBase p hp) x 10 hx) T₁₆) hdisjoint) D₂₇)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (Z₀ Zinf : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (P₁₁ : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      (hypersurfaceToBase p hp) C seed 11 Z₀ Zinf)
    (zeroIso : Z₀.val.subscheme ≅
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subscheme)
    (zero_over : zeroIso.hom ≫
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subschemeι =
      Z₀.val.subschemeι)
    (infinityIso : Zinf.val.subscheme ≅
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆).val.subscheme)
    (infinity_over : infinityIso.hom ≫
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆).val.subschemeι =
      Zinf.val.subschemeι)
    (T₈ : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈)
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (P₈ : let hdisjoint :=
      (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
        p hp hne D₈ T₈)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 12
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp) D₈
      (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
            p hp hne D₈ T₈) hdisjoint) D₁₂)
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  let S := VoisinDegreeTenPointPencilData.of_projectiveLineRankTwoPencilData
    (hypersurfaceToBase p hp) C seed T₁₆.completion.datum
    (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) T₁₆)
    (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
      p hp hne
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) T₁₆)
    D₂₇ P₁₆ D₃ D₈ h₈₃ Z₀ Zinf P₁₁ zeroIso zero_over infinityIso infinity_over
    (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData p hp hne D₈ T₈)
    (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
      p hp hne D₈ T₈) D₁₂ P₈
  exact voisinDegreeTenPointSteps_of_completion_and_cycleClasses p hp x hx T₁₆.completion h
    hfirst hsecond S rfl cycle₂₇ cycle₃ cycle₁₂

/- The raw projective-line Serre construction already contains every finite
   subscheme and endpoint identification needed by the point-specific Voisin
   argument.  This wrapper exposes its numerical conclusion directly: after
   the endpoint cycle classes are supplied, the constructed chain yields an
   effective degree-four cycle. -/
theorem effective_degree_four_of_embeddedResidualData_and_projectiveLinePencil
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (T₁₆ : DegreeTenTransverseCubicIntersectionEmbeddingData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (D₂₇ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 27)
    (P₁₆ : let hdisjoint :=
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
        p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 27
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp)
          T₁₆.completion.datum
          (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
            p hp hne
            (finiteSubschemeDatumOfClosedPointOfResidueDegree
              (hypersurfaceToBase p hp) x 10 hx) T₁₆) hdisjoint) D₂₇)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (h₈₃ : Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (Z₀ Zinf : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (P₁₁ : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      (hypersurfaceToBase p hp) C seed 11 Z₀ Zinf)
    (zeroIso : Z₀.val.subscheme ≅
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subscheme)
    (zero_over : zeroIso.hom ≫
      (degreeEightAndDegreeThreeDatum (hypersurfaceToBase p hp) D₈ D₃ h₈₃).val.subschemeι =
      Z₀.val.subschemeι)
    (infinityIso : Zinf.val.subscheme ≅
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆).val.subscheme)
    (infinity_over : infinityIso.hom ≫
      (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) T₁₆).val.subschemeι =
      Zinf.val.subschemeι)
    (T₈ : DegreeEightTransverseQuadricIntersectionEmbeddingData p hp D₈)
    (D₁₂ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 12)
    (P₈ : let hdisjoint :=
      (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint
        p hp hne D₈ T₈)
      FiniteSubschemeDatumPencil (hypersurfaceToBase p hp) 12
        (finiteSubschemeDatumOfTwoDisjointData (hypersurfaceToBase p hp) D₈
          (degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData
            p hp hne D₈ T₈) hdisjoint) D₁₂)
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hh : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3)
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) T₁₆.completion.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    ∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
  have hz₁₀ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (Finsupp.single x 1) = 10 := by
    rw [effectiveCycle_degree_single, hx]
  exact effective_degree_four_of_voisin_degree_ten_point_steps
    (hypersurfaceToBase p hp) h (Finsupp.single x 1) hh hz₁₀
      (voisinDegreeTenPointSteps_of_embeddedResidualData_and_projectiveLinePencil
        p hp hne x hx T₁₆ D₂₇ P₁₆ D₃ D₈ h₈₃ C seed Z₀ Zinf P₁₁
        zeroIso zero_over infinityIso infinity_over T₈ D₁₂ P₈ h hfirst hsecond
        cycle₂₇ cycle₃ cycle₁₂)

end PfaffianDescent
