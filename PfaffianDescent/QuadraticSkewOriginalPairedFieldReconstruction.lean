import PfaffianDescent.QuadraticSkewConjugateInverseParameters
import PfaffianDescent.QuadraticSkewGroundInverseQuadraticEvaluation
/-! SOURCE ONLY / UNVERIFIED. The split reconstruction is transferred
through the actual original paired basis and the actual descended residual.
All statements concern arbitrary field-valued evaluations of the original
coordinate algebra; no equality of scheme maps is a premise. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module QuarticNet OriginalBridge ActualSecant
open AmbientResidual MixedNonvanishing
open scoped BigOperators
universe u v w
variable {k E : Type u} {L : Type v}
variable [Field k] [Field E] [Field L] [Algebra k E]

def pairedValues (C : Basis (Fin 4) E (Fin 4 → E))
    (f : E →+* L) (w : Fin 4 → L) : Fin 4 → L :=
  fun i => (pairedInverseCoordinates C i).eval₂ f w

theorem pairedValues_eq_inverse_matrix_mulVec
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L) (w : Fin 4 → L) :
    pairedValues C f w = (((basisCoordinateMatrix C)⁻¹).map f).mulVec w := by
  ext i
  change (linearSubstitution (basisCoordinateMatrix C)⁻¹ (X i)).eval₂ f w = _
  rw [linearSubstitution_X]
  simp [linearCoordinate, Matrix.mulVec, dotProduct, MvPolynomial.eval₂_sum]

theorem original_matrix_mul_pairedValues
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L) (w : Fin 4 → L) :
    ((basisCoordinateMatrix C).map f).mulVec (pairedValues C f w) = w := by
  rw [pairedValues_eq_inverse_matrix_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (basisCoordinateMatrix_isUnit C),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem transformed_cubic_eval_pairedValues
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (w : Fin 4 → L) (FE : MvPolynomial (Fin 4) E) :
    (linearSubstitution (basisCoordinateMatrix C) FE).eval₂ f (pairedValues C f w) =
      FE.eval₂ f w := by
  letI : Algebra E L := f.toAlgebra
  change aeval (pairedValues C f w) (linearSubstitution (basisCoordinateMatrix C) FE) =
    aeval w FE
  rw [aeval_linearSubstitution]
  change aeval (((basisCoordinateMatrix C).map f).mulVec (pairedValues C f w)) FE = _
  rw [original_matrix_mul_pairedValues]

private theorem planeT_field_eval (f : E →+* L) (t z : L) :
    (planeT.{u, w} : MvPolynomial SecantPlaneIndex.{w} E).eval₂ f
      (fun i => ![t, z] i.down) = t := by
  change MvPolynomial.eval₂ f
    (fun i : ULift.{w} (Fin 2) => ![t, z] i.down)
    (MvPolynomial.X (ULift.up (0 : Fin 2))) = t
  exact MvPolynomial.eval₂_X f
    (fun i : ULift.{w} (Fin 2) => ![t, z] i.down) (ULift.up (0 : Fin 2))

private theorem planeU_field_eval (f : E →+* L) (t z : L) :
    (planeU.{u, w} : MvPolynomial SecantPlaneIndex.{w} E).eval₂ f
      (fun i => ![t, z] i.down) = z := by
  change MvPolynomial.eval₂ f
    (fun i : ULift.{w} (Fin 2) => ![t, z] i.down)
    (MvPolynomial.X (ULift.up (1 : Fin 2))) = z
  exact MvPolynomial.eval₂_X f
    (fun i : ULift.{w} (Fin 2) => ![t, z] i.down) (ULift.up (1 : Fin 2))

theorem actualSecantA_eval₂
    (f : E →+* L) (α β : E) (G : MvPolynomial (Fin 4) E)
    (t u : L) :
    (actualSecantA α β G).eval₂ f (fun i => ![t, u] i.down) =
      leftMixedValue (mappedMixedCoefficients f G) 1
        (t + f α * u) 1 (t + f β * u) := by
  rw [actualSecantA_eq_leftMixedValue]
  simp [leftMixedValue, mappedMixedCoefficients, planeT_field_eval, planeU_field_eval]

theorem actualSecantB_eval₂
    (f : E →+* L) (α β : E) (G : MvPolynomial (Fin 4) E)
    (t u : L) :
    (actualSecantB α β G).eval₂ f (fun i => ![t, u] i.down) =
      rightMixedValue (mappedMixedCoefficients f G) 1
        (t + f α * u) 1 (t + f β * u) := by
  rw [actualSecantB_eq_rightMixedValue]
  simp [rightMixedValue, mappedMixedCoefficients, planeT_field_eval, planeU_field_eval]

theorem originalRawResidual_eval₂
    (f : E →+* L) (α β : E) (G : MvPolynomial (Fin 4) E)
    (t u : L) :
    (fun i => (originalRawResidual α β G i).eval₂ f (fun j => ![t, u] j.down)) =
      residualCoordinates (mappedMixedCoefficients f G)
        (t + f α * u) (t + f β * u) := by
  ext i
  fin_cases i <;>
    simp [originalRawResidual, residualCoordinates, actualSecantA_eval₂,
      actualSecantB_eval₂, planeT_field_eval, planeU_field_eval]

theorem originalAmbientResidual_eval₂
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (α β : E) (G : MvPolynomial (Fin 4) E) (t u : L) :
    (fun i => (originalAmbientResidual C α β G i).eval₂ f
        (fun j => ![t, u] j.down)) =
      ((basisCoordinateMatrix C).map f).mulVec
        (residualCoordinates (mappedMixedCoefficients f G)
          (t + f α * u) (t + f β * u)) := by
  rw [originalAmbientResidual_eq_matrix_mulVec]
  rw [← originalRawResidual_eval₂ f α β G t u]
  ext i
  simp [Matrix.mulVec, dotProduct, MvPolynomial.eval₂_sum] <;> rfl

/-- Reconstruction is in the ORIGINAL ambient coordinates. The scalar is
explicit, and its invertibility follows from actual secant nonvanishing.
The displayed algebraic inputs are outputs of the original-input factory. -/
theorem descended_original_residual_field_reconstruction
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (α β δ : E) (hαβ : α ≠ β) (hδ : δ ≠ 0)
    (FE : MvPolynomial (Fin 4) E) (hFE : FE.IsHomogeneous 3)
    (hLeft : linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : linearSubstitution (basisCoordinateMatrix C) FE ∈
      Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)))
    (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
      MvPolynomial.C δ * originalAmbientResidual C α β
        (linearSubstitution (basisCoordinateMatrix C) FE) i)
    (w : Fin 4 → L) (hFw : FE.eval₂ f w = 0)
    (hv₀ : pairedValues C f w 0 ≠ 0) (hv₂ : pairedValues C f w 2 ≠ 0)
    (hB : rightMixedValue (mappedMixedCoefficients f
        (linearSubstitution (basisCoordinateMatrix C) FE))
      1 (pairedValues C f w 1 / pairedValues C f w 0)
      1 (pairedValues C f w 3 / pairedValues C f w 2) ≠ 0) :
    ∃ c : L, c ≠ 0 ∧
      (fun i => (r i).eval₂ (f.comp (algebraMap k E))
        (fun j => ![inverseT (f α) (f β) (pairedValues C f w),
          inverseU (f α) (f β) (pairedValues C f w)] j.down)) = c • w := by
  let G := linearSubstitution (basisCoordinateMatrix C) FE
  let v := pairedValues C f w
  let c₀ := rightMixedValue (mappedMixedCoefficients f G)
    1 (v 1 / v 0) 1 (v 3 / v 2) / v 0
  have hGv : G.eval₂ f v = 0 :=
    (transformed_cubic_eval_pairedValues C f w FE).trans hFw
  have hFc : splitCubicValue (mappedMixedCoefficients f G)
      (v 0) (v 1) (v 2) (v 3) = 0 := by
    rw [← eval₂_eq_splitCubicValue f v G (linearSubstitution_homogeneous _ hFE) hLeft hRight]
    exact hGv
  have hαβ' : f α ≠ f β := (RingHom.injective f).ne hαβ
  have hraw := residualCoordinates_at_inverseParameters
    (mappedMixedCoefficients f G) (f α) (f β) hαβ' v hv₀ hv₂ hFc
  have hambient := originalAmbientResidual_eval₂ C f α β G
    (inverseT (f α) (f β) v) (inverseU (f α) (f β) v)
  rw [hraw, Matrix.mulVec_smul, original_matrix_mul_pairedValues] at hambient
  have hfδ : f δ ≠ 0 := by
    intro h
    apply hδ
    apply RingHom.injective f
    simpa only [map_zero] using h
  refine ⟨f δ * c₀, reconstruction_scalar_ne_zero (f δ) _ _
    hfδ hB hv₀, ?_⟩
  have hrEval (i : Fin 4) :
      (r i).eval₂ (f.comp (algebraMap k E))
          (fun j => ![inverseT (f α) (f β) v, inverseU (f α) (f β) v] j.down) =
        f δ * (originalAmbientResidual C α β G i).eval₂ f
          (fun j => ![inverseT (f α) (f β) v, inverseU (f α) (f β) v] j.down) := by
    rw [← MvPolynomial.eval₂_map, hr i, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  ext i
  rw [hrEval, congrFun hambient i]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, c₀]

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
