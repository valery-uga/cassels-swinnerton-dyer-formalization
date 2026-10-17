import PfaffianDescent.QuadraticSkewGroundInverseQuadraticEvaluation
/-! SOURCE ONLY / UNVERIFIED. Original-input factory: every coordinate,
normal-form, nonvanishing, descent and evaluation certificate used by the
actual scheme forward map is derived from the original smooth cubic and
its actual exchanged skew-line projector. No rationality certificate is
an input and no BirationalOver endpoint is claimed in this algebra packet. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
open QuarticNet PairedFrame OriginalBridge MixedNormalForm ActualSecant MixedNonvanishing
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Retained witnesses and exact original identities for use by BOTH
composites of the genuine scheme map. Smoothness supplies nonvanishing. -/
theorem original_matching_exists_secant_polynomial_data
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
    ∃ C : Basis (Fin 4) E (Fin 4 → E), ∃ α δ : E,
    ∃ r : Fin 4 → MvPolynomial SecantPlaneIndex k,
    ∃ Q R_T R_U : MvPolynomial (Fin 4) k,
      matchingEdgeProjectorMatrix C = P ∧
      (∀ i : Fin 2, ∀ j : Fin 4,
        C (Fin.natAdd 2 i) j = σ (C (Fin.castAdd 2 i) j)) ∧
      α ≠ σ α ∧ δ ≠ 0 ∧
      Q.IsHomogeneous 2 ∧ R_T.IsHomogeneous 2 ∧ R_U.IsHomogeneous 2 ∧
      MvPolynomial.map (algebraMap k E) Q = pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2 ∧
      MvPolynomial.map (algebraMap k E) R_T = MvPolynomial.C (α - σ α)⁻¹ *
        (MvPolynomial.C α * pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0 -
          MvPolynomial.C (σ α) * pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2) ∧
      MvPolynomial.map (algebraMap k E) R_U = MvPolynomial.C (α - σ α)⁻¹ *
        (pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2 -
          pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0) ∧
      let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
      (∀ m, MvPolynomial.map (algebraMap k E) (r m) =
        MvPolynomial.C δ * originalAmbientResidual C α (σ α) G m) ∧
      leftSecantPolynomial G ≠ 0 ∧ rightSecantPolynomial G ≠ 0 := by
  obtain ⟨C, hC, hPair⟩ := actual_matching_exists_paired_projector_frame E P B hP σ hExchange
  have hσsq := galois_involution_of_finrank_two σ hσ h₂
  obtain ⟨α, hα⟩ := nontrivial_automorphism_exists_nonfixed_element σ hσ
  obtain ⟨δ, hδ, r, hr⟩ := original_ground_cubic_varying_residual_descends
    h₂ σ hσ C hPair α F
  have hX := pairedInverseCoordinates_exchange σ hσsq C hPair
  obtain ⟨Q, R_T, R_U, hQhom, hThom, hUhom, hQ, hT, hU⟩ :=
    InverseQuadratics.conjugate_inverse_quadratics_descend σ hσ h₂ α hα
      (pairedInverseCoordinates C) (pairedInverseCoordinates_homogeneous C)
      (hX 0) (hX 1) (hX 2) (hX 3)
  have hSecants := original_smooth_cubic_secant_polynomials_ne_zero F hF hF₀ C P hC hLines
  exact ⟨C, α, δ, r, Q, R_T, R_U, hC, hPair, hα, hδ,
    hQhom, hThom, hUhom, hQ, hT, hU, hr, hSecants.1, hSecants.2⟩

/-- Direct output matching the genuine forward-scheme interface. N is
chosen as minus the ACTUAL Q evaluation; its nonvanishing is proved from
original Smooth, and the scalar a is the ground unit -1. -/
theorem original_matching_exists_ground_forward_polynomial_data
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
    ∃ R : SecantPlaneIndex → MvPolynomial (Fin 4) k,
    ∃ r : Fin 4 → MvPolynomial SecantPlaneIndex k,
    ∃ N : MvPolynomial SecantPlaneIndex k,
      (∀ i, (R i).IsHomogeneous 2) ∧ Q ≠ 0 ∧ r ≠ 0 ∧ N ≠ 0 ∧
      MvPolynomial.eval₂ MvPolynomial.C r F = 0 ∧
      MvPolynomial.eval₂ MvPolynomial.C r Q = MvPolynomial.C (-1 : k) * N ∧
      ∀ i, MvPolynomial.eval₂ MvPolynomial.C r (R i) =
        MvPolynomial.eval₂ MvPolynomial.C r Q * MvPolynomial.X i := by
  obtain ⟨C, α, δ, r, Q, R_T, R_U, hC, hPair, hα, hδ,
      hQhom, hThom, hUhom, hQ, hT, hU, hr, hA, hB⟩ :=
    original_matching_exists_secant_polynomial_data.{u, _, u, u}
      E h₂ P B hP σ hσ hExchange F hF hF₀ hLines
  let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
  have hEvalQ := descended_inverse_denominator_evaluation_ne_zero C α (σ α) hα δ hδ
    G hA hB r hr Q hQ
  have hEvalR := descended_inverse_numerator_evaluations C α (σ α) hα δ G r hr Q R_T R_U hQ hT hU
  have hr₀ := descended_originalAmbientResidual_ne_zero C α (σ α) G
    (actualSecantB_ne_zero α (σ α) hα G hB) δ hδ r hr
  have hEvalF := descended_original_residual_vanishes_on_ground_cubic F hF C P hC hLines
    α (σ α) δ r hr
  have hQ₀ : Q ≠ 0 := by
    intro hz
    exact hEvalQ (by rw [hz, MvPolynomial.eval₂_zero])
  let R : SecantPlaneIndex → MvPolynomial (Fin 4) k := fun i => ![R_T, R_U] i.down
  let N := -MvPolynomial.eval₂ MvPolynomial.C r Q
  refine ⟨Q, hQhom, R, r, N, ?_, hQ₀, hr₀, neg_ne_zero.mpr hEvalQ, hEvalF, ?_, ?_⟩
  · intro i
    rcases i with ⟨i⟩
    fin_cases i
    · exact hThom
    · exact hUhom
  · simp [N]
  · intro i
    rcases i with ⟨i⟩
    fin_cases i
    · exact hEvalR.1
    · exact hEvalR.2

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
