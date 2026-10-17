import PfaffianDescent.QuadraticSkewOriginalAmbientResidualNonzero
import AllCharacteristics.HomogeneousSpecialization
/-! SOURCE ONLY / UNVERIFIED. The descended varying residual lies on
the SAME original ground cubic, as a polynomial identity, not only after
specializing ground field points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module
open QuarticNet OriginalBridge MixedNormalForm ActualSecant MixedNonvanishing
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
variable {k E : Type u} [Field k] [Field E] [Algebra k E]


private theorem coefficientMap_comp_C {J : Type v} :
    (MvPolynomial.map (σ := J) (algebraMap k E)).comp
      (MvPolynomial.C : k →+* MvPolynomial J k) =
    (MvPolynomial.C : E →+* MvPolynomial J E).comp (algebraMap k E) := by
  apply RingHom.ext
  intro a
  exact MvPolynomial.map_C _ _

theorem originalRawResidual_eq_secantCoordinates
    (α β : E) (G : MvPolynomial (Fin 4) E) :
    originalRawResidual α β G = residualCoordinates (mappedMixedCoefficients C G)
      (planeT + C α * planeU) (planeT + C β * planeU) := by
  ext i
  fin_cases i <;> simp [originalRawResidual, residualCoordinates,
    actualSecantA_eq_leftMixedValue, actualSecantB_eq_rightMixedValue]

/-- The equation vanishes identically over the actual polynomial ring. -/
theorem actual_mixed_equation_vanishes_on_raw_residual
    (α β : E) (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    MvPolynomial.eval₂ C (originalRawResidual α β G) G = 0 := by
  rw [eval₂_eq_splitCubicValue C _ G hG hLeft hRight,
    originalRawResidual_eq_secantCoordinates]
  exact residualCoordinates_on_cubic (mappedMixedCoefficients C G)
    (planeT + C α * planeU) (planeT + C β * planeU)

theorem original_extended_equation_vanishes_on_ambient_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (FE : MvPolynomial (Fin 4) E) (hFE : FE.IsHomogeneous 3)
    (hLeft : linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    MvPolynomial.eval₂ MvPolynomial.C
      (originalAmbientResidual C α β (linearSubstitution (basisCoordinateMatrix C) FE)) FE = 0 := by
  have h := actual_mixed_equation_vanishes_on_raw_residual α β
    (linearSubstitution (basisCoordinateMatrix C) FE)
    (linearSubstitution_homogeneous _ hFE) hLeft hRight
  change MvPolynomial.aeval (originalRawResidual α β
    (linearSubstitution (basisCoordinateMatrix C) FE))
    (linearSubstitution (basisCoordinateMatrix C) FE) = 0 at h
  rw [aeval_linearSubstitution] at h
  rw [originalAmbientResidual_eq_matrix_mulVec]
  change MvPolynomial.eval₂ MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (basisCoordinateMatrix C i j) *
      originalRawResidual α β (linearSubstitution (basisCoordinateMatrix C) FE) j) FE = 0
  simpa only [aeval_def, MvPolynomial.algebraMap_eq] using h

/-- Ground identity required by the actual forward scheme construction.
The descent coordinates are outputs of original_ground_cubic_varying_residual_descends;
no new normal-form/evaluation premise is necessary for the application. -/
theorem descended_original_residual_vanishes_on_ground_cubic
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (C : Basis (Fin 4) E (Fin 4 → E)) (P : Matrix (Fin 4) (Fin 4) E)
    (hC : matchingEdgeProjectorMatrix C = P)
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal)
    (α β δ : E) (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ m, MvPolynomial.map (algebraMap k E) (r m) = MvPolynomial.C δ *
      originalAmbientResidual C α β
        (linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)) m) :
    MvPolynomial.eval₂ MvPolynomial.C r F = 0 := by
  let FE := MvPolynomial.map (algebraMap k E) F
  let G := linearSubstitution (basisCoordinateMatrix C) FE
  obtain ⟨hLeft, hRight⟩ := original_cubic_paired_coordinate_line_memberships C P hC FE hLines
  have hRaw : MvPolynomial.eval₂ MvPolynomial.C (originalAmbientResidual C α β G) FE = 0 :=
    original_extended_equation_vanishes_on_ambient_residual C α β FE (hF.map _) hLeft hRight
  apply MvPolynomial.map_injective (algebraMap k E) (algebraMap k E).injective
  rw [map_zero, hom_eval₂]
  rw [coefficientMap_comp_C]
  have hcoords : (fun i => MvPolynomial.map (algebraMap k E) (r i)) =
      (fun i => MvPolynomial.C δ * originalAmbientResidual C α β G i) := by
    funext i
    exact hr i
  rw [hcoords]
  have hEvalMap : MvPolynomial.eval₂ (MvPolynomial.C.comp (algebraMap k E))
      ((fun i => MvPolynomial.C δ * originalAmbientResidual C α β G i)) F =
      MvPolynomial.eval₂ MvPolynomial.C
        ((fun i => MvPolynomial.C δ * originalAmbientResidual C α β G i)) FE := by
    dsimp only [FE]
    rw [MvPolynomial.eval₂_map]
  rw [hEvalMap]
  have hScale : MvPolynomial.eval₂ MvPolynomial.C
      (fun i => MvPolynomial.C δ * originalAmbientResidual C α β G i) FE =
      (MvPolynomial.C δ) ^ 3 *
        MvPolynomial.eval₂ MvPolynomial.C (originalAmbientResidual C α β G) FE := by
    have hScaledFamily :
        (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex E) •
          originalAmbientResidual C α β G =
        (fun i => MvPolynomial.C δ * originalAmbientResidual C α β G i) := by
      funext i
      change (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex E) • originalAmbientResidual C α β G i =
        MvPolynomial.C δ * originalAmbientResidual C α β G i
      exact smul_eq_mul _ _
    have hNative := AllCharacteristics.eval₂_homogeneous_smul FE (hF.map _)
      MvPolynomial.C (originalAmbientResidual C α β G) (MvPolynomial.C δ)
    rw [hScaledFamily] at hNative
    exact hNative
  rw [hScale, hRaw, mul_zero]

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
