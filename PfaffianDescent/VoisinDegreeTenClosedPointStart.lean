import PfaffianDescent.VoisinDegreeTenFiniteDatumStart
import PfaffianDescent.VoisinDegreeTenSmoothStart
import AllCharacteristics.ClosedPointFiniteSubscheme
import AllCharacteristics.ClosedPointFiniteSubschemeCycle

/-!
# Starting Voisin's first residual from Coray's degree-ten point

Coray's degree-ten alternative supplies a closed point, whereas the
complete-intersection part of Voisin's construction takes a rank-ten finite
subscheme datum.  This module makes that conversion explicit.  The remaining
inputs are exactly the geometric choices still to be proved: a regular pair
of cubic sections and a transverse three-cubic intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a smooth cubic, Coray's degree-ten closed point has the two successive
avoiding line sections needed to form the rank-sixteen datum for Voisin's
first residual. -/
theorem nonempty_degreeTenClosedPoint_rankSixteenCompletion_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) :
    Nonempty (DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx)) := by
  exact nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    p hp hne
    (finiteSubschemeDatumOfClosedPointOfResidueDegree
      (hypersurfaceToBase p hp) x 10 hx)

/-- The completed rank-sixteen datum has exactly Coray's degree-ten point
and its two avoiding degree-three line sections as its finite cycle. -/
theorem degreeTenClosedPoint_rankSixteenCompletion_cycle
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx)) :
    finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.datum =
      Finsupp.single x 1 +
        finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first +
          finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second := by
  rw [C.datum_cycle]
  rw [finiteSubschemeDatumCycle_closedPoint_of_residueDegree
    (hypersurfaceToBase p hp) x 10 hx]

/-- Once the two avoiding line sections have the same reference cycle, the
completed datum has the first endpoint form `z₁₀ + 2h` used by Voisin's
cubic pencil. -/
theorem degreeTenClosedPoint_rankSixteenCompletion_cycle_eq_of_lineSectionCycles
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first = h)
    (hsecond : finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second = h) :
    finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.datum =
      Finsupp.single x 1 + 2 • h := by
  rw [degreeTenClosedPoint_rankSixteenCompletion_cycle p hp x hx C, hfirst, hsecond]
  simpa [two_nsmul] using (add_assoc (Finsupp.single x 1) h h)

/-- Coray's degree-ten closed point, together with one completed transverse
three-cubic intersection, supplies the finite étale rank-eleven residual for
Voisin's rank-two step.  The hypothesis records just the selected geometric
triple, rather than a prime-intermediate or uniform-transversality surrogate. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_completion_and_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx))
    (coordinates : let D := C.datum
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
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_coordinates
    p q r hp hq hr hne hrel hregular
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    C coordinates htransverse

/-- Starting with Coray's degree-ten point, Voisin's associated-component
avoidance for one selected cubic--cubic curve selects the third cubic and
produces the finite étale degree-eleven residual.  This keeps the remaining
Lemma 3.3 and Bertini inputs in their point-specific form: no assertion that
all intermediate curves are prime is introduced. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_completion_and_avoids_associatedPrimes
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hne : p ≠ 0)
    (hrel : IsRelPrime p q)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx))
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        (∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) a 3,
            Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r ∉ P))
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_avoids_associatedPrimes
    p q hp hq hne hrel
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    C coordinates htransverse

/-- Coray's degree-ten point needs only one selected regular transverse third
cubic after its two line-section completion. This is the exact point-specific
Bertini input used by the first residual construction. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_completion_and_selected_regular_transverse_cubic
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx))
    (selected : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell r : MvPolynomial (Fin 4) K)
        (hr : r.IsHomogeneous 3),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_regular_transverse_cubic
      p q hp hq hne hrel
      (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
      C selected

/-- The Frobenius version starts directly from Coray's degree-ten closed
point and returns the finite-flat rank-eleven residual, without imposing
étaleness on the selected complete intersection. -/
theorem exists_degreeTenClosedPoint_residualDatum_of_completion_and_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx))
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne
          (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel)
          hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  exact exists_degreeTenResidualDatum_of_completion_and_selected_coordinates_of_frobenius
    p q r hp hq hr hne hrel hregular
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    C coordinates hfrob

/-- For Coray's degree-ten closed point, an embedding of its completed
rank-sixteen datum in the selected three-cubic intersection gives the
rank-eleven residual directly.  This presents the remaining first-residual
geometry as scheme-theoretic containment rather than as an auxiliary choice
of normalized coordinates. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) C j hj

/-- The scheme-theoretic first residual of Coray's completed degree-ten
point is automatically disjoint from that completion.  Thus the support
condition at the first endpoint of Voisin's cubic pencil follows from the
actual complete-intersection embedding, rather than being an extra premise
for the pencil construction. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_and_disjoint_of_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular C.datum j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_, ?_⟩
  · exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
      p q r hp hq hr hne hq0 hrel hregular C.datum j hj
  · exact (disjoint_finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular C.datum j hj).symm

/-- The same closed-point interface has a Frobenius form, which needs no
étaleness assertion in order to construct the finite-flat degree-eleven
residual. -/
theorem exists_degreeTenClosedPoint_residualDatum_of_completeIntersectionEmbedding_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  exact
    exists_degreeTenResidualDatum_of_completion_and_completeIntersectionEmbedding_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) C j hj hfrob

/-- On a smooth cubic, Coray's degree-ten point feeds directly into the
selected-prime first residual.  The primeness of the surface and the two
avoiding line sections are supplied internally; the remaining inputs are the
selected intermediate cubic and its transverse third cubic. -/
theorem exists_degreeTenClosedPoint_residualDatum_of_smooth_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hselected : ∃ C : DegreeTenRankSixteenCompletion p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx),
      DegreeTenSelectedPrimeIntermediate p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) C)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  exact exists_degreeTenResidualDatum_of_smooth_cubic_and_selected_prime_intermediate
    p hp hne
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    hselected htransverse

/-- The smooth-cubic closed-point entry point also retains the finite
étaleness of the rank-eleven residual required for Voisin's rank-two step. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_smooth_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hselected : ∃ C : DegreeTenRankSixteenCompletion p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx),
      DegreeTenSelectedPrimeIntermediate p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) C)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_and_selected_prime_intermediate
    p hp hne
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    hselected htransverse

/-- A degree-ten closed point on a smooth cubic supplies the rank-ten datum
used by the first residual construction.  Once the selected cubics form a
regular transverse complete intersection, their rank-eleven residual is an
actual finite subscheme of the original surface. -/
theorem exists_degreeTenClosedPoint_residualDatum_of_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  exact exists_degreeTenResidualDatum_of_prime_cubic_and_prime_intermediate
    p hp hne
    (finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx)
    hprime₁ hprime₂ htransverse

/-- Coray's degree-ten point already provides the only non-line-section input
to Voisin's first residual.  After the two avoiding line sections have been
chosen from the prime cubic, the section-selection argument requires just one
selected prime intermediate cubic, rather than primeness for every cubic in
the linear system. -/
theorem exists_degreeTenClosedPoint_residualDatum_of_prime_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hselected : let D₁₀ :=
        finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
      let C := Classical.choice
        (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
      let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  let D₁₀ :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
  exact exists_degreeTenResidualDatum_of_prime_cubic_and_selected_prime_intermediate
    p hp hne D₁₀ hprime hselected htransverse

/-- Starting from Coray's degree-ten closed point, the selected-prime first
residual is finite étale as well as of degree eleven.  Consequently the input
to Voisin's rank-two construction is an actual finite étale scheme, once the
displayed selected-intersection geometry has been constructed. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_prime_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hselected : let D₁₀ :=
        finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
      let C := Classical.choice
        (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
      let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (a : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) a) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) a = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D₁₀ :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_prime_cubic_and_selected_prime_intermediate
      p hp hne D₁₀ hprime hselected htransverse

/-- Starting with Coray's degree-ten point, the first residual follows from
Lemma 3.3 only for the regular cubic section that the smooth cubic itself
selects.  The rank-drop estimate chooses the third cubic, and the transverse
complete intersection then gives the finite étale degree-eleven residual. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_regularCubicSectionData_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hdrop : ∀ S : DegreeTenRegularCubicSectionData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx),
      DegreeTenCompletionThirdCubicFinrankDrop p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D₁₀ :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
  obtain ⟨S⟩ := nonempty_degreeTenRegularCubicSectionData_of_smooth_cubic
    p hp hne D₁₀
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_regularCubicSectionData_and_finrank_drop
    p hp hne D₁₀ S (by simpa only [D₁₀] using hdrop S) htransverse

/-- Coray's degree-ten closed point, together with Voisin's rank-drop and
transverse-choice inputs, gives the actual completed degree-sixteen scheme
and a finite étale degree-eleven residual disjoint from it.  This is the
scheme-level first endpoint needed before constructing Voisin's first pencil. -/
theorem exists_degreeTenClosedPoint_completion_and_residualDatum_and_toBase_etale_and_disjoint_of_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hdrop : ∀ S : DegreeTenRegularCubicSectionEmbeddingData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx),
      DegreeTenCompletionThirdCubicFinrankDrop p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx) S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ C : DegreeTenRankSixteenCompletion p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx),
      ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
        Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        Disjoint
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let D₁₀ :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 10 hx
  simpa only [D₁₀] using
    exists_degreeTenCompletion_and_residualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
      p hp hne D₁₀ hdrop htransverse

/-- Coray's degree-ten closed point feeds directly into the concrete first
Bertini datum.  The datum records one chosen transverse complete intersection,
so this entry point retains the actual existential form of Voisin's choice. -/
theorem exists_degreeTenClosedPoint_residualDatum_and_toBase_etale_of_transverseCubicIntersectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx)) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      p hp hne
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) T

/-- Coray's degree-ten point and one selected transverse third cubic give
the completed degree-sixteen scheme and a finite étale degree-eleven
residual disjoint from it.  Only the selected complete intersection is
required to be transverse. -/
theorem exists_degreeTenClosedPoint_completion_and_residualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    (T : DegreeTenRegularCubicSectionSelectedThirdCubicData p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) S) :
    ∃ C : DegreeTenRankSixteenCompletion p hp
        (finiteSubschemeDatumOfClosedPointOfResidueDegree
          (hypersurfaceToBase p hp) x 10 hx),
      ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
        C = S.completion ∧
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
        Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        Disjoint
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
            C.datum))
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨R, hdegree, hetale, hdisjoint⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
      p hp hne
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx) S T
  exact ⟨S.completion, R, rfl, hdegree, hetale, hdisjoint⟩

end PfaffianDescent
