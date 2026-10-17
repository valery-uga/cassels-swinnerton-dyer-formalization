import PfaffianDescent.QuadraticSkewOriginalAmbientResidualEquation
import PfaffianDescent.QuadraticSkewInverseQuadraticDescent
/-! SOURCE ONLY / UNVERIFIED. Exact evaluations of the descended original
inverse quadratics on the internally constructed original secant residual.
These are polynomial identities required by the actual scheme maps. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module
open QuarticNet OriginalBridge MixedNormalForm ActualSecant MixedNonvanishing
universe u v w
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

theorem eval₂_linearCoordinate_polynomial
    (M : Matrix (Fin 4) (Fin 4) E) (v : Fin 4 → MvPolynomial SecantPlaneIndex E) (i : Fin 4) :
    MvPolynomial.eval₂ MvPolynomial.C v (linearCoordinate M i) =
      (M.map MvPolynomial.C).mulVec v i := by
  simp [linearCoordinate, Matrix.mulVec, dotProduct, MvPolynomial.eval₂_sum]

theorem actual_inverse_linear_forms_on_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) (i : Fin 4) :
    MvPolynomial.eval₂ MvPolynomial.C (originalAmbientResidual C α β G)
      (pairedInverseCoordinates C i) = originalRawResidual α β G i := by
  change MvPolynomial.eval₂ MvPolynomial.C (originalAmbientResidual C α β G)
    (linearSubstitution (basisCoordinateMatrix C)⁻¹ (X i)) = _
  rw [linearSubstitution_X, eval₂_linearCoordinate_polynomial,
    originalAmbientResidual_inverse_matrix_mulVec]

theorem actual_inverse_linear_forms_on_scaled_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β δ : E)
    (G : MvPolynomial (Fin 4) E) (i : Fin 4) :
    MvPolynomial.eval₂ MvPolynomial.C ((MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{v} E) • originalAmbientResidual C α β G)
      (pairedInverseCoordinates C i) = MvPolynomial.C δ * originalRawResidual α β G i := by
  rw [AllCharacteristics.eval₂_homogeneous_smul _ (pairedInverseCoordinates_homogeneous C i),
    pow_one, actual_inverse_linear_forms_on_residual]

/-- Exact Q evaluation. In the ground ring its negative will serve as N,
so there is no additional scalar/square descent obligation. -/
theorem inverse_denominator_on_scaled_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β δ : E)
    (G : MvPolynomial (Fin 4) E) :
    MvPolynomial.eval₂ MvPolynomial.C ((MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{v} E) • originalAmbientResidual C α β G)
      (pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2) =
      -(MvPolynomial.C δ ^ 2 * actualSecantA α β G * actualSecantB α β G) := by
  rw [eval₂_mul, actual_inverse_linear_forms_on_scaled_residual,
    actual_inverse_linear_forms_on_scaled_residual]
  simp [originalRawResidual] <;> ring

/-- Exact numerator identities before coefficient descent. -/
theorem inverse_numerators_on_scaled_residual
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E) (hαβ : α ≠ β) (δ : E)
    (G : MvPolynomial (Fin 4) E) :
    let v := (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{v} E) • originalAmbientResidual C α β G
    let x := pairedInverseCoordinates C
    MvPolynomial.eval₂ MvPolynomial.C v
      (MvPolynomial.C (α - β)⁻¹ * (MvPolynomial.C α * x 3 * x 0 - MvPolynomial.C β * x 1 * x 2)) =
        MvPolynomial.eval₂ MvPolynomial.C v (x 0 * x 2) * planeT ∧
    MvPolynomial.eval₂ MvPolynomial.C v
      (MvPolynomial.C (α - β)⁻¹ * (x 1 * x 2 - x 3 * x 0)) =
        MvPolynomial.eval₂ MvPolynomial.C v (x 0 * x 2) * planeU := by
  have hδ : (MvPolynomial.C (α - β)⁻¹ : MvPolynomial SecantPlaneIndex.{v} E) *
      (MvPolynomial.C α - MvPolynomial.C β) = 1 := by
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hαβ), map_one]
  dsimp only
  constructor
  · simp only [eval₂_mul, eval₂_sub, eval₂_C,
      actual_inverse_linear_forms_on_scaled_residual]
    simp only [originalRawResidual, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination
      (-MvPolynomial.C δ ^ 2 * actualSecantA α β G * actualSecantB α β G * planeT) * hδ
  · simp only [eval₂_mul, eval₂_sub, eval₂_C,
      actual_inverse_linear_forms_on_scaled_residual]
    simp only [originalRawResidual, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination
      (-MvPolynomial.C δ ^ 2 * actualSecantA α β G * actualSecantB α β G * planeU) * hδ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal renaming of the two lifted variables preserves the native
secant, so a zero identity transports between independent index universes. -/
private theorem inverseActualSecantA_zero_of_other_index_universe
    (α β : E) (G : MvPolynomial (Fin 4) E)
    (h : actualSecantA.{u, v} α β G = 0) :
    actualSecantA.{u, w} α β G = 0 := by
  let lift : SecantPlaneIndex.{v} → SecantPlaneIndex.{w} := fun i => ⟨i.down⟩
  have ht : MvPolynomial.rename lift
      (planeT.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      (planeT.{u, w} : MvPolynomial SecantPlaneIndex.{w} E) := by
    exact MvPolynomial.rename_X lift (ULift.up (0 : Fin 2))
  have hu : MvPolynomial.rename lift
      (planeU.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      (planeU.{u, w} : MvPolynomial SecantPlaneIndex.{w} E) := by
    exact MvPolynomial.rename_X lift (ULift.up (1 : Fin 2))
  have hr : MvPolynomial.rename lift (actualSecantA.{u, v} α β G) =
      actualSecantA.{u, w} α β G := by
    rw [actualSecantA_eq_leftMixedValue, actualSecantA_eq_leftMixedValue]
    simp only [leftMixedValue, ActualSecant.mappedMixedCoefficients,
      map_add, map_mul, map_pow, map_one, MvPolynomial.rename_C, ht, hu]
  have hmap := congrArg (MvPolynomial.rename lift) h
  rw [hr, map_zero] at hmap
  exact hmap

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal renaming of the two lifted variables preserves the native
secant, so a zero identity transports between independent index universes. -/
private theorem inverseActualSecantB_zero_of_other_index_universe
    (α β : E) (G : MvPolynomial (Fin 4) E)
    (h : actualSecantB.{u, v} α β G = 0) :
    actualSecantB.{u, w} α β G = 0 := by
  let lift : SecantPlaneIndex.{v} → SecantPlaneIndex.{w} := fun i => ⟨i.down⟩
  have ht : MvPolynomial.rename lift
      (planeT.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      (planeT.{u, w} : MvPolynomial SecantPlaneIndex.{w} E) := by
    exact MvPolynomial.rename_X lift (ULift.up (0 : Fin 2))
  have hu : MvPolynomial.rename lift
      (planeU.{u, v} : MvPolynomial SecantPlaneIndex.{v} E) =
      (planeU.{u, w} : MvPolynomial SecantPlaneIndex.{w} E) := by
    exact MvPolynomial.rename_X lift (ULift.up (1 : Fin 2))
  have hr : MvPolynomial.rename lift (actualSecantB.{u, v} α β G) =
      actualSecantB.{u, w} α β G := by
    rw [actualSecantB_eq_rightMixedValue, actualSecantB_eq_rightMixedValue]
    simp only [rightMixedValue, ActualSecant.mappedMixedCoefficients,
      map_add, map_mul, map_pow, map_one, MvPolynomial.rename_C, ht, hu]
  have hmap := congrArg (MvPolynomial.rename lift) h
  rw [hr, map_zero] at hmap
  exact hmap

/-- The denominator polynomial cannot vanish on this varying residual. -/
theorem inverse_denominator_on_scaled_residual_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E) (hαβ : α ≠ β)
    (δ : E) (hδ : δ ≠ 0) (G : MvPolynomial (Fin 4) E)
    (hA : leftSecantPolynomial G ≠ 0) (hB : rightSecantPolynomial G ≠ 0) :
    MvPolynomial.eval₂ MvPolynomial.C ((MvPolynomial.C δ : MvPolynomial SecantPlaneIndex.{v} E) • originalAmbientResidual C α β G)
      (pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2) ≠ 0 := by
  have hAother : actualSecantA α β G ≠ 0 := actualSecantA_ne_zero α β hαβ G hA
  have hBother : actualSecantB α β G ≠ 0 := actualSecantB_ne_zero α β hαβ G hB
  have hAv : actualSecantA.{u, v} α β G ≠ 0 := by
    intro hz
    exact hAother (inverseActualSecantA_zero_of_other_index_universe α β G hz)
  have hBv : actualSecantB.{u, v} α β G ≠ 0 := by
    intro hz
    exact hBother (inverseActualSecantB_zero_of_other_index_universe α β G hz)
  rw [inverse_denominator_on_scaled_residual]
  exact neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 (MvPolynomial.C_ne_zero.mpr hδ))
      hAv)
    hBv)

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
