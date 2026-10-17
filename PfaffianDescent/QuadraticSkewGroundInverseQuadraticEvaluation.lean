import PfaffianDescent.QuadraticSkewOriginalInverseQuadraticEvaluation
/-! SOURCE ONLY / UNVERIFIED. Original quadratic descent and original
residual descent are now used to prove the exact GROUND polynomial
identities accepted by the genuine forward-scheme interface. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module
open QuarticNet OriginalBridge MixedNormalForm ActualSecant MixedNonvanishing
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E]


private theorem inverseEvaluationCoefficientMap_comp_C {J : Type v} :
    (MvPolynomial.map (σ := J) (algebraMap k E)).comp
      (MvPolynomial.C : k →+* MvPolynomial J k) =
    (MvPolynomial.C : E →+* MvPolynomial J E).comp (algebraMap k E) := by
  apply RingHom.ext
  intro a
  exact MvPolynomial.map_C _ _

theorem original_polynomial_evaluation_map
    (q : MvPolynomial (Fin 4) k) (r : Fin 4 → MvPolynomial SecantPlaneIndex k) :
    MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r q) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.map (algebraMap k E) (r i))
        (MvPolynomial.map (algebraMap k E) q) := by
  rw [hom_eval₂, eval₂_map, inverseEvaluationCoefficientMap_comp_C]

theorem descended_inverse_denominator_evaluation
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β δ : E)
    (G : MvPolynomial (Fin 4) E)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β G i)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2) :
    MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r Q) =
      -(MvPolynomial.C δ ^ 2 * actualSecantA α β G * actualSecantB α β G) := by
  rw [original_polynomial_evaluation_map, hQ]
  have hcoords : (fun i => MvPolynomial.map (algebraMap k E) (r i)) =
      (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{_} E) • originalAmbientResidual C α β G := by
    funext i
    exact hr i
  rw [hcoords, inverse_denominator_on_scaled_residual]

theorem descended_inverse_denominator_evaluation_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E) (hαβ : α ≠ β)
    (δ : E) (hδ : δ ≠ 0) (G : MvPolynomial (Fin 4) E)
    (hA : leftSecantPolynomial G ≠ 0) (hB : rightSecantPolynomial G ≠ 0)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β G i)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2) :
    MvPolynomial.eval₂ MvPolynomial.C r Q ≠ 0 := by
  intro hz
  have hMapped := congrArg (MvPolynomial.map (algebraMap k E)) hz
  rw [map_zero, original_polynomial_evaluation_map, hQ] at hMapped
  have hcoords : (fun i => MvPolynomial.map (algebraMap k E) (r i)) =
      (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{_} E) •
        originalAmbientResidual C α β G := by
    funext i
    exact hr i
  rw [hcoords] at hMapped
  exact inverse_denominator_on_scaled_residual_ne_zero C α β hαβ δ hδ G hA hB hMapped

private theorem inverseEvaluationCoefficientMap_mul_X {J : Type v}
    (q : MvPolynomial J k) (i : J) :
    MvPolynomial.map (algebraMap k E) (q * MvPolynomial.X i) =
      MvPolynomial.map (algebraMap k E) q * MvPolynomial.X i := by
  rw [map_mul, MvPolynomial.map_X]

/-- Both descended inverse numerators evaluate to the denominator times
the actual ground affine coordinate. -/
theorem descended_inverse_numerator_evaluations
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E) (hαβ : α ≠ β) (δ : E)
    (G : MvPolynomial (Fin 4) E)
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β G i)
    (Q R_T R_U : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (hT : MvPolynomial.map (algebraMap k E) R_T =
      MvPolynomial.C (α - β)⁻¹ *
        (MvPolynomial.C α * pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0 -
          MvPolynomial.C β * pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2))
    (hU : MvPolynomial.map (algebraMap k E) R_U =
      MvPolynomial.C (α - β)⁻¹ *
        (pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2 -
          pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0)) :
    MvPolynomial.eval₂ MvPolynomial.C r R_T = MvPolynomial.eval₂ MvPolynomial.C r Q * X (ULift.up 0) ∧
    MvPolynomial.eval₂ MvPolynomial.C r R_U = MvPolynomial.eval₂ MvPolynomial.C r Q * X (ULift.up 1) := by
  have hcoords : (fun i => MvPolynomial.map (algebraMap k E) (r i)) =
      (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{_} E) • originalAmbientResidual C α β G := by
    funext i
    exact hr i
  have hExact := inverse_numerators_on_scaled_residual C α β hαβ δ G
  have hMappedT :
      MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r R_T) =
        MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r Q) *
          MvPolynomial.X (σ := SecantPlaneIndex) (ULift.up (0 : Fin 2)) := by
    rw [original_polynomial_evaluation_map, original_polynomial_evaluation_map,
      hQ, hT, hcoords]
    exact hExact.1
  have hMappedU :
      MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r R_U) =
        MvPolynomial.map (algebraMap k E) (MvPolynomial.eval₂ MvPolynomial.C r Q) *
          MvPolynomial.X (σ := SecantPlaneIndex) (ULift.up (1 : Fin 2)) := by
    rw [original_polynomial_evaluation_map, original_polynomial_evaluation_map,
      hQ, hU, hcoords]
    exact hExact.2
  constructor
  · apply MvPolynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    exact hMappedT.trans
      (inverseEvaluationCoefficientMap_mul_X (MvPolynomial.eval₂ MvPolynomial.C r Q)
        (show SecantPlaneIndex from ULift.up (0 : Fin 2))).symm
  · apply MvPolynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    exact hMappedU.trans
      (inverseEvaluationCoefficientMap_mul_X (MvPolynomial.eval₂ MvPolynomial.C r Q)
        (show SecantPlaneIndex from ULift.up (1 : Fin 2))).symm

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
