import PfaffianDescent.VoisinDegreeEightHomogeneousCurve

/-!
# Recovered degree-eight residual interfaces

These source declarations restore the existential final-Bertini APIs consumed
by the generic specialization route.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The final Bertini conclusion with both quadrics chosen together. -/
def DegreeEightRegularTransverseQuadricPairExists
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
  ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
    q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
    q ≠ 0 ∧ IsRelPrime p q ∧
    ∃ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2),
      r.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- A regular pair produces Voisin's effective degree-four residual cycle. -/
theorem exists_effectiveDegreeFourCycle_of_regularQuadricPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightRegularQuadricPairExists p hp D₈) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx⟩ :=
    cubicFiniteSubscheme_normalized_coordinates p hp D₈.val.subschemeι
  obtain ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hregular⟩ := hpair x hxsurj
  exact finiteSubschemeDatum_degree_eight_complement_cycle_degree_four_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D₈
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- The uniform rank-drop condition gives the same effective cycle on a
smooth cubic. -/
theorem exists_effectiveDegreeFourCycle_of_smooth_cubic_and_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hdrop : DegreeEightSecondQuadricFinrankDrop p hp D₈) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hne).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  exact exists_effectiveDegreeFourCycle_of_regularQuadricPair p hp hne D₈
    (DegreeEightRegularQuadricPairExists.of_finrankDrop_of_prime_cubic
      p hp D₈ hpprime hdrop)

/-- A transverse pair produces the finite étale degree-four residual. -/
theorem exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_regularTransverseQuadricPair
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hpair : DegreeEightRegularTransverseQuadricPairExists p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_chart p hp D₈.val.subschemeι
  obtain ⟨q, hq, hqvan, hq0, hrel, r, hr, hrvan, hregular, htransverse⟩ :=
    hpair x hxsurj
  let T := DegreeEightTransverseQuadricIntersectionEmbeddingData.ofNormalizedChart
    p q r hp hq hr D₈ hrel hregular
    ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩ htransverse
  exact ⟨degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData p hp hne D₈ T,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_cycle_degree p hp hne D₈ T,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_toBase_etale p hp hne D₈ T,
    degreeFourResidualDatumOfTransverseQuadricIntersectionEmbeddingData_disjoint p hp hne D₈ T⟩

end PfaffianDescent
