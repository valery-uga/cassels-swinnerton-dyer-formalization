import PfaffianDescent.ActualQuarticDualTensorCoordinates
import PfaffianDescent.HomogeneousEvaluationFieldExtension
import PfaffianDescent.QuarticGeneralTangentQuadrics

/-! SOURCE ONLY, UNVERIFIED. Converse quadratic dimension for the SAME
actual finite algebra and supplied dual/embedding-indexed coordinates.
Full extension-field kernels are proved before flat dimension descent. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module TrivSqZeroExt
open scoped TensorProduct
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A] [Module.Finite k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- The ENTIRE actual scalar-extended quadratic kernel, including all
K-coefficient equations and nilpotents, is carried to the tangent kernel
by the actual conjugate coordinate basis. This equality is proved internally. -/
theorem actualQuarticTensor_quadratic_kernel_coordinate_map
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = inl (b r) + inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K)) :
    let hs := conjugate_basis_span b full
    let B := conjugateBasis full b hs
    let M := basisCoordinateMatrix B
    let U := conjugateTangentMatrix full b v hs
    (homogeneousVanishingPolynomialSubmodule (K := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) 2).map
        (linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit B)).toLinearEquiv.toLinearMap =
      homogeneousTangentQuadrics U := by
  classical
  let hs := conjugate_basis_span b full
  let B := conjugateBasis full b hs
  let M := basisCoordinateMatrix B
  let U := conjugateTangentMatrix full b v hs
  let e := linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit B)
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  change (homogeneousVanishingPolynomialSubmodule (K := K) y 2).map
    e.toLinearEquiv.toLinearMap = homogeneousTangentQuadrics U
  ext G
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨hFhom, hFzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff y 2 F).mp hF
    have hRaw : aeval (R := K) (fourTangentRawCoordinates U)
        (linearSubstitution M F) = 0 :=
      (actualQuarticTensor_homogeneous_equation_iff eA x b v hx full F 2 hFhom).mpr hFzero
    apply (mem_homogeneousTangentQuadrics U _).mpr
    refine ⟨linearSubstitution_homogeneous M hFhom, ?_⟩
    intro row
    exact (fourTangentRawEvaluation_apply U (linearSubstitution M F) row).symm.trans
      (congrFun hRaw row)
  · intro hG
    obtain ⟨hGhom, hGzero⟩ := (mem_homogeneousTangentQuadrics U G).mp hG
    let F := e.symm G
    have hFG : linearSubstitution M F = G := e.apply_symm_apply G
    have hFhom : F.IsHomogeneous 2 := by
      change (linearSubstitution M⁻¹ G).IsHomogeneous 2
      exact linearSubstitution_homogeneous M⁻¹ hGhom
    have hRaw : aeval (R := K) (fourTangentRawCoordinates U)
        (linearSubstitution M F) = 0 := by
      rw [hFG]
      funext row
      exact (fourTangentRawEvaluation_apply U G row).trans (hGzero row)
    have hFzero : aeval (R := K) y F = 0 :=
      (actualQuarticTensor_homogeneous_equation_iff eA x b v hx full F 2 hFhom).mp hRaw
    exact ⟨F, (mem_homogeneousVanishingPolynomialSubmodule_iff y 2 F).mpr
      ⟨hFhom, hFzero⟩, hFG⟩

/-- Nonzero skew row weights on this SAME actual embedding-indexed matrix
force at least three genuine ground-field quadratic equations of A. No
ground kernel dimension or field-extension comparison is an input. -/
theorem actualQuarticSkew_ground_quadratic_finrank_three
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = inl (b r) + inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0)
    (hskew : let U := conjugateTangentMatrix full b v (conjugate_basis_span b full)
      ∀ r s, l r * U r s = -(l s * U s r)) :
    3 ≤ finrank k (homogeneousVanishingPolynomialSubmodule (K := k) x 2) := by
  classical
  let hs := conjugate_basis_span b full
  let B := conjugateBasis full b hs
  let M := basisCoordinateMatrix B
  let U := conjugateTangentMatrix full b v hs
  let e := linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit B)
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  have hlne : l ≠ 0 := by
    intro hz
    exact hl 0 (congrFun hz 0)
  have hrel (r s : Fin 4) : l r * U r s + l s * U s r = 0 := by
    rw [hskew r s]
    exact neg_add_cancel _
  have hKernel : 3 ≤ finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)) :=
    three_le_finrank_ker_tangentQuadricEvaluation_of_weighted_relation U l hlne
      (weightedTangentQuadricEvaluation_eq_zero_of_relations U l
        (hrel 0 1) (hrel 0 2) (hrel 0 3) (hrel 1 2) (hrel 1 3) (hrel 2 3))
  have hTangent : 3 ≤ finrank K (homogeneousTangentQuadrics U) := by
    rw [fullTangentQuadric_finrank U (conjugateTangentMatrix_diagonal full b v hs)]
    exact hKernel
  have hMap : (homogeneousVanishingPolynomialSubmodule (K := K) y 2).map
      e.toLinearEquiv.toLinearMap = homogeneousTangentQuadrics U :=
    actualQuarticTensor_quadratic_kernel_coordinate_map eA x b v hx full
  have hDim : finrank K (homogeneousTangentQuadrics U) =
      finrank k (homogeneousVanishingPolynomialSubmodule (K := k) x 2) := by
    calc
      _ = finrank K ((homogeneousVanishingPolynomialSubmodule (K := K) y 2).map
          e.toLinearEquiv.toLinearMap) := congrArg (finrank K) hMap.symm
      _ = finrank K (homogeneousVanishingPolynomialSubmodule (K := K) y 2) :=
        e.toLinearEquiv.finrank_map_eq _
      _ = _ := homogeneousVanishingPolynomialSubmodule_fieldExtension_finrank (K := K) x 2
  exact hTangent.trans_eq hDim

end PfaffianDescent.QuarticNet
