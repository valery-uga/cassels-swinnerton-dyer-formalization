import PfaffianDescent.QuadraticSkewOriginalResidualSecondRingIdentity
import PfaffianDescent.QuadraticSkewCommonInjectiveFieldEvaluation
import PfaffianDescent.QuadraticSkewActualMatchingSecantPolynomialData
/-! SOURCE ONLY / UNVERIFIED. Actual original-input assembly of the two
coordinate-ring inverse identities. The common injective field, original
paired frame, residual coordinates, ground inverse quadratics and nonzero
principal denominator are ALL constructed from the original smooth cubic
and exchanged skew-line projector. No desired inverse-map or rationality
certificate is a premise. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module AlgebraicGeometry QuarticNet OriginalBridge AmbientResidual
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The actual ring equivalence has inverse-coordinate map equal to the
canonical localization lift of the original inverse numerators. Its forward
map is constructed from the literal original residual in the proof. -/
theorem actual_matching_exists_inverse_domain_ring_equivalence
    (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
    (h₂ : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (hExchange : P.map σ.toRingHom = 1 - P)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    ∃ Q : MvPolynomial (Fin 4) k, ∃ hQ : Q.IsHomogeneous 2,
    ∃ R : PlaneIndex → MvPolynomial (Fin 4) k,
    ∃ hR : ∀ i, (R i).IsHomogeneous 2,
    ∃ N : PlanePolynomial k, N ≠ 0 ∧
    ∃ e : PlaneLocalization N ≃+* Localization.Away
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR N),
      e.toRingHom = inverseLocalizationHom N
        (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR) := by
  obtain ⟨C, α, δ, r, Q, R_T, R_U, hC, hPair, hα, hδ,
      hQhom, hThom, hUhom, hQmap, hTmap, hUmap, hr, hA, hB⟩ :=
    original_matching_exists_secant_polynomial_data.{u, _, u, u}
      E h₂ P B hP σ hσ hExchange F hF hF₀ hLines
  let r : Fin 4 → PlanePolynomial k := r
  let FE := MvPolynomial.map (algebraMap k E) F
  let G := linearSubstitution (basisCoordinateMatrix C) FE
  have hSecantQ := descended_inverse_denominator_evaluation_ne_zero C α (σ α) hα δ hδ
    G hA hB r hr Q hQmap
  have hSecantR := descended_inverse_numerator_evaluations C α (σ α) hα δ G
    r hr Q R_T R_U hQmap hTmap hUmap
  have hFr := descended_original_residual_vanishes_on_ground_cubic F hF C P hC hLines
    α (σ α) δ r hr
  let N : PlanePolynomial k := -Q.eval₂ MvPolynomial.C r
  have hN : N ≠ 0 := neg_ne_zero.mpr hSecantQ
  have hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r =
      MvPolynomial.C (-1 : k) * N := by
    change Q.eval₂ MvPolynomial.C r =
      MvPolynomial.C (-1 : k) * (-Q.eval₂ MvPolynomial.C r)
    rw [map_neg, map_one, neg_mul, one_mul, neg_neg]
  let R := originalInverseNumerators R_T R_U
  let hR := originalInverseNumerators_homogeneous R_T R_U hThom hUhom
  have hRatios : ∀ i, (R i).eval₂ (algebraMap k (PlanePolynomial k)) r =
      X i * Q.eval₂ (algebraMap k (PlanePolynomial k)) r := by
    rintro ⟨i⟩
    fin_cases i
    · change R_T.eval₂ MvPolynomial.C r =
        X (ULift.up (0 : Fin 2)) * Q.eval₂ MvPolynomial.C r
      exact hSecantR.1.trans (mul_comm _ _)
    · change R_U.eval₂ MvPolynomial.C r =
        X (ULift.up (1 : Fin 2)) * Q.eval₂ MvPolynomial.C r
      exact hSecantR.2.trans (mul_comm _ _)
  have hPairLines := original_cubic_paired_coordinate_line_memberships C P hC FE hLines
  let A := CoordinateRing (equationIdeal F hF)
  letI : IsDomain A := by
    change IsDomain (MvPolynomial (Fin 4) k ⧸ Ideal.span ({F} : Set (MvPolynomial (Fin 4) k)))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF₀)
  let d := commonFieldEvaluation k A E
  let θ := inverseCoordinateRingHom (equationIdeal F hF) Q hQhom R hR
  let φ := forwardChartRingHom F hF (localizedResidualCoordinates N r)
    (by
      exact (localizedResidualCoordinates_eval N r F).trans
        ((congrArg (algebraMap (PlanePolynomial k) (PlaneLocalization N)) hFr).trans
          (map_zero _))) Q
      (localizedResidualCoordinates_quadratic_isUnit N r Q (-1) (neg_ne_zero.mpr one_ne_zero) hQeval)
  have hfirst : φ.comp θ = algebraMap (PlanePolynomial k) (PlaneLocalization N) :=
    residual_forward_ring_comp_inverse F hF Q hQhom N r hFr (-1)
      (neg_ne_zero.mpr one_ne_zero) hQeval R hR hRatios
  have hsecond : (inverseLocalizationHom (S := PlaneLocalization N)
      (T := Localization.Away (θ N)) N θ).comp φ =
      algebraMap (QuadraticChartRing (equationIdeal F hF) Q) (Localization.Away (θ N)) :=
    original_residual_second_ring_identity F hF d.coordinate d.coordinate_injective
      d.coefficient C α (σ α) δ hα hδ hPairLines.1 hPairLines.2 r hr Q R_T R_U
      hQhom hThom hUhom hQmap hTmap hUmap N hN hFr (-1)
        (neg_ne_zero.mpr one_ne_zero) hQeval hRatios
  let e := chartLocalizationRingEquiv (S := PlaneLocalization N)
    (T := Localization.Away (θ N)) N θ φ hfirst hsecond
  exact ⟨Q, hQhom, R, hR, N, hN, e, rfl⟩

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
