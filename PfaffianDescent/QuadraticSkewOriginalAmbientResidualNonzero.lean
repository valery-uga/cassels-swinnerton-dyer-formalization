import PfaffianDescent.QuadraticSkewOriginalAmbientResidualDescent
/-! SOURCE ONLY / UNVERIFIED. The residual is in the original ambient
coordinates; its nonvanishing is derived using the actual invertible
basis matrix, without assuming a residual-coordinate certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.QuadraticSkewRationality.AmbientResidual
open MvPolynomial Module
open QuarticNet MixedNonvanishing ActualSecant
universe u v w
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

theorem nontrivial_automorphism_exists_nonfixed_element
    (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl) : ∃ α : E, α ≠ σ α := by
  by_contra h
  push_neg at h
  apply hσ
  ext a
  exact (h a).symm

def originalRawResidual (α β : E) (G : MvPolynomial (Fin 4) E) :
    Fin 4 → MvPolynomial SecantPlaneIndex E :=
  ![actualSecantB α β G, actualSecantB α β G * (planeT + C α * planeU),
    -actualSecantA α β G, -actualSecantA α β G * (planeT + C β * planeU)]

theorem originalAmbientResidual_eq_matrix_mulVec
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) :
    originalAmbientResidual C α β G =
      ((basisCoordinateMatrix C).map MvPolynomial.C).mulVec (originalRawResidual α β G) := by
  funext m
  simp [originalAmbientResidual, leftEndpoint, rightEndpoint,
    originalRawResidual, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.map_apply, basisCoordinateMatrix] <;> ring

theorem originalAmbientResidual_inverse_matrix_mulVec
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) :
    (((basisCoordinateMatrix C)⁻¹).map MvPolynomial.C).mulVec
      (originalAmbientResidual C α β G) = originalRawResidual α β G := by
  rw [originalAmbientResidual_eq_matrix_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (basisCoordinateMatrix_isUnit C),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]


/-- The literal secant polynomial is preserved by renaming the two lifted
variables, so zero transports between the independently quantified universes. -/
private theorem actualSecantB_zero_of_other_index_universe
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

theorem originalAmbientResidual_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) (hB : actualSecantB α β G ≠ 0) :
    originalAmbientResidual C α β G ≠ 0 := by
  intro hz
  have hback := originalAmbientResidual_inverse_matrix_mulVec C α β G
  rw [hz, Matrix.mulVec_zero] at hback
  have h₀ := congrFun hback 0
  apply hB
  apply actualSecantB_zero_of_other_index_universe α β G
  simpa only [originalRawResidual, Matrix.cons_val_zero, Pi.zero_apply] using h₀.symm

/-- Any coefficientwise descent of the internally constructed nonzero
residual remains nonzero; this includes the output of the previous file. -/
theorem descended_originalAmbientResidual_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (α β : E)
    (G : MvPolynomial (Fin 4) E) (hB : actualSecantB α β G ≠ 0)
    (δ : E) (hδ : δ ≠ 0) (r : Fin 4 → MvPolynomial SecantPlaneIndex k)
    (hr : ∀ m, MvPolynomial.map (algebraMap k E) (r m) =
      MvPolynomial.C δ * originalAmbientResidual C α β G m) : r ≠ 0 := by
  intro hz
  apply originalAmbientResidual_ne_zero C α β G hB
  funext m
  have h := hr m
  rw [hz, Pi.zero_apply, map_zero] at h
  have hδC : (MvPolynomial.C δ : MvPolynomial SecantPlaneIndex E) ≠ 0 := by
    exact MvPolynomial.C_ne_zero.mpr hδ
  exact (mul_eq_zero.mp h.symm).resolve_left hδC

end PfaffianDescent.QuadraticSkewRationality.AmbientResidual
