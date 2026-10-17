import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalizationResidue

noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]

/-- The distinguished linear chart coordinate has exactly zero derivative. -/
@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedChartCoordinate_snd
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K) (hunit : IsUnit (aeval J ell)) :
    (aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) ell).snd = 0 := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell ell J hell hunit]
  rfl

/-- Simultaneous normalization multiplies whole square-zero jets by units;
the residue and derivative are retained together. -/
def cubicClosedPointSerreSurfaceJetCotangent_fullNormalizationEquiv
    (uj : Fin 3 → (CubicSurfaceFirstJet K)ˣ) (uv : Fin 8 → Kˣ) :
    ((Fin 3 → CubicSurfaceFirstJet K) × (Fin 8 → K)) ≃ₗ[K]
      ((Fin 3 → CubicSurfaceFirstJet K) × (Fin 8 → K)) where
  toFun z := (fun i => (↑(uj i)⁻¹ : CubicSurfaceFirstJet K) ^ 3 * z.1 i,
    fun i => (↑(uv i)⁻¹ : K) ^ 3 * z.2 i)
  invFun z := (fun i => (↑(uj i) : CubicSurfaceFirstJet K) ^ 3 * z.1 i,
    fun i => (↑(uv i) : K) ^ 3 * z.2 i)
  left_inv z := by
    apply Prod.ext <;> funext i <;>
      simp only [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  right_inv z := by
    apply Prod.ext <;> funext i <;>
      simp only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  map_add' z w := by
    apply Prod.ext <;> funext i <;> exact mul_add _ _ _
  map_smul' c z := by
    apply Prod.ext <;> funext i
    · change _ * (c • z.1 i) = c • (_ * z.1 i)
      exact Algebra.mul_smul_comm c _ _
    · change _ * (c • z.2 i) = c • (_ * z.2 i)
      exact Algebra.mul_smul_comm c _ _

/-- Full three-jet/eight-value interpolation survives the actual common
linear chart normalization. No derivative-only simplification is used. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_fullInterpolation_normalized
    (ell : MvPolynomial (Fin 4) K)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (v : Fin 8 → Fin 4 → K)
    (hj : ∀ i, IsUnit (aeval (J i) ell))
    (hv : ∀ i, aeval (v i) ell ≠ 0)
    (hfull : Function.Surjective
      (fun q : homogeneousSubmodule (Fin 4) K 3 =>
        ((fun i => aeval (J i) q.1), (fun i => aeval (v i) q.1)))) :
    Function.Surjective
      (fun q : homogeneousSubmodule (Fin 4) K 3 =>
        ((fun i => aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
          ell (J i) (hj i)) q.1),
         (fun i => aeval (fun j => (aeval (v i) ell)⁻¹ * v i j) q.1))) := by
  let uj : Fin 3 → (CubicSurfaceFirstJet K)ˣ := fun i => (hj i).unit
  let uv : Fin 8 → Kˣ := fun i => Units.mk0 (aeval (v i) ell) (hv i)
  let e := cubicClosedPointSerreSurfaceJetCotangent_fullNormalizationEquiv uj uv
  intro z
  obtain ⟨q, hq⟩ := hfull (e.symm z)
  refine ⟨q, ?_⟩
  have ht :
      ((fun i => aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
          ell (J i) (hj i)) q.1),
       (fun i => aeval (fun j => (aeval (v i) ell)⁻¹ * v i j) q.1)) =
      e ((fun i => aeval (J i) q.1), (fun i => aeval (v i) q.1)) := by
    apply Prod.ext
    · funext i
      exact cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous
        ell (J i) (hj i) q.1 q.2
    · funext i
      exact cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous q.1 q.2 _ (v i)
  exact ht.trans ((congrArg e hq).trans (e.apply_symm_apply z))

end PfaffianDescent
