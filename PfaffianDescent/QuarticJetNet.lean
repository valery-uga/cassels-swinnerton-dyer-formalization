import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.QuarticGeneralTangentQuadrics
import PfaffianDescent.QuarticSemilinearNormalization
import PfaffianDescent.PolynomialCoefficientRetraction

/-!
# From the selected ground-field jet to a skew tangent net

This assembles the linear part of the degree-four construction.  Three
ground-field quadrics through the selected affine jet remain independent
after scalar extension and coordinate change, giving the tangent-kernel
dimension required for semilinear skew normalization.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

universe u

variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

theorem homogeneousAffineDualPoint_eq_dual (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv : v 0 = 0) :
    homogeneousAffineDualPoint (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ) =
      fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i) := by
  funext i
  fin_cases i <;> simp [homogeneousAffineDualPoint, hp, hv]

theorem exists_three_ground_quadrics (p v : Fin 4 → L) (hp : p 0 = 1) (hv : v 0 = 0)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ))) :
    ∃ Q : Fin 3 → MvPolynomial (Fin 4) k,
      LinearIndependent k Q ∧ (∀ i, (Q i).IsHomogeneous 2) ∧
      ∀ i, aeval (R := k) (S₁ := DualNumber L)
        (fun j => TrivSqZeroExt.inl (p j) + TrivSqZeroExt.inr (v j)) (Q i) = 0 := by
  obtain ⟨Q, hQI, hQ, hvan⟩ :=
    exists_three_homogeneous_quadrics_of_affine_jet_dimension
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ) hdim
  refine ⟨Q, hQI, hQ, ?_⟩
  intro i
  rw [← homogeneousAffineDualPoint_eq_dual p v hp hv]
  exact hvan i

theorem polynomial_linearIndependent_map {ι σ : Type*} [Fintype ι]
    (Q : ι → MvPolynomial σ k) (hQ : LinearIndependent k Q) :
    LinearIndependent K (fun i => map (algebraMap k K) (Q i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  apply (Module.forall_dual_apply_eq_zero_iff k (c i)).mp
  intro phi
  apply (Fintype.linearIndependent_iff.mp hQ) (fun j => phi (c j)) _ i
  have h := congrArg (polynomialCoefficientMap phi) hc
  rw [map_sum] at h
  simpa only [smul_eq_C_mul, polynomialCoefficientMap_C_mul_map, map_zero] using h

theorem independent_conjugate_quadrics
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (Q : Fin 3 → MvPolynomial (Fin 4) k) (hQI : LinearIndependent k Q)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hvan : ∀ i, aeval (R := k) (S₁ := DualNumber L)
      (fun j => TrivSqZeroExt.inl (p j) + TrivSqZeroExt.inr (v j)) (Q i) = 0) :
    3 ≤ Module.finrank K
      (LinearMap.ker (tangentQuadricEvaluationLinearMap
        (conjugateTangentMatrix e p v hspan))) := by
  let M := basisCoordinateMatrix (conjugateBasis e p hspan)
  let U := conjugateTangentMatrix e p v hspan
  let G : Fin 3 → MvPolynomial (Fin 4) K :=
    fun i => linearSubstitution M (map (algebraMap k K) (Q i))
  have hGI : LinearIndependent K G :=
    (polynomial_linearIndependent_map Q hQI).map'
      (linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit _)).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (linearSubstitutionEquiv M (basisCoordinateMatrix_isUnit _)).injective)
  have hG (i : Fin 3) : G i ∈ homogeneousTangentQuadrics U :=
    (mem_homogeneousTangentQuadrics U _).mpr
      ⟨linearSubstitution_homogeneous M ((hQ i).map (algebraMap k K)),
        homogeneous_jet_vanishes_on_conjugates e p v hspan (Q i) 2 (hQ i) (hvan i)⟩
  let G' : Fin 3 → homogeneousTangentQuadrics U := fun i => ⟨G i, hG i⟩
  have hGI' : LinearIndependent K G' :=
    LinearIndependent.of_comp (homogeneousTangentQuadrics U).subtype hGI
  letI : Module.Finite K (homogeneousTangentQuadrics U) :=
    Module.Finite.equiv (fullTangentQuadricEquiv U
      (conjugateTangentMatrix_diagonal e p v hspan))
  have hdimH : 3 ≤ Module.finrank K (homogeneousTangentQuadrics U) := by
    simpa only [Fintype.card_fin] using hGI'.fintype_card_le_finrank
  exact three_le_tangentQuadric_kernel_of_homogeneous U
    (conjugateTangentMatrix_diagonal e p v hspan) hdimH

theorem conjugate_skew_normalization_from_ground_jets [Normal k K] [Infinite K]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L) (hp : p 0 = 1) (hv : v 0 = 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ))) :
    ∃ l : Fin 4 → K, (∀ i, l i ≠ 0) ∧ ∀ i j,
      l i * conjugateTangentMatrix e p v hspan i j =
        -(l j * conjugateTangentMatrix e p v hspan j i) := by
  obtain ⟨Q, hQI, hQ, hvan⟩ := exists_three_ground_quadrics p v hp hv hdim
  exact skew_normalization_of_transitive_covariance
    (conjugateTangentMatrix e p v hspan)
    (conjugateTangentMatrix_diagonal e p v hspan)
    (independent_conjugate_quadrics e p v hspan Q hQI hQ hvan)
    (conjugateTangentMatrix_transitive_covariance e p v hspan)

end QuarticNet
end PfaffianDescent
