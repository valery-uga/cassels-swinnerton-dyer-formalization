import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.QuarticTangentInterpolation

/-!
# All homogeneous quadrics through four tangent jets

For four coordinate vertices, every homogeneous quadric through the four
dual-number points has zero square coefficients.  Thus its remaining six
coefficients are exactly the kernel of the tangent-evaluation map used in
the coordinate calculation.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

variable {K : Type*} [Field K]

noncomputable def homogeneousTangentQuadrics (U : Fin 4 → Fin 4 → K) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  homogeneousSubmodule (Fin 4) K 2 ⊓
    ⨅ i : Fin 4, LinearMap.ker (aeval (tangentDualPoint U i)).toLinearMap

theorem mem_homogeneousTangentQuadrics (U : Fin 4 → Fin 4 → K)
    (F : MvPolynomial (Fin 4) K) :
    F ∈ homogeneousTangentQuadrics U ↔
      F.IsHomogeneous 2 ∧ ∀ i : Fin 4, aeval (tangentDualPoint U i) F = 0 := by
  simp only [homogeneousTangentQuadrics, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

noncomputable def offDiagonalCoefficientEmbedding :
    (Fin 6 → K) →ₗ[K] (Fin 10 → K) where
  toFun q := ![0, q 0, q 1, q 2, 0, q 3, q 4, 0, q 5, 0]
  map_add' q r := by
    funext i
    fin_cases i <;> simp
  map_smul' a q := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

theorem offDiagonalCoefficientEmbedding_injective :
    Function.Injective (offDiagonalCoefficientEmbedding (K := K)) := by
  intro q r h
  funext i
  fin_cases i <;>
    first | exact congrFun h 1 | exact congrFun h 2 | exact congrFun h 3 |
      exact congrFun h 5 | exact congrFun h 6 | exact congrFun h 8

noncomputable def offDiagonalQuadrics :
    (Fin 6 → K) →ₗ[K] MvPolynomial (Fin 4) K :=
  homogeneousAffineQuadrics.comp offDiagonalCoefficientEmbedding

theorem offDiagonalQuadrics_injective :
    Function.Injective (offDiagonalQuadrics (K := K)) := by
  intro q r h
  apply offDiagonalCoefficientEmbedding_injective
  apply homogeneousAffineQuadrics_injective
  exact h

theorem offDiagonalQuadrics_homogeneous (q : Fin 6 → K) :
    (offDiagonalQuadrics q).IsHomogeneous 2 :=
  homogeneousAffineQuadrics_homogeneous _

theorem homogeneousAffineQuadrics_expansion (q : Fin 10 → K) :
    homogeneousAffineQuadrics q =
      C (q 0) * X 0 ^ 2 + C (q 1) * X 0 * X 1 +
      C (q 2) * X 0 * X 2 + C (q 3) * X 0 * X 3 +
      C (q 4) * X 1 ^ 2 + C (q 5) * X 1 * X 2 +
      C (q 6) * X 1 * X 3 + C (q 7) * X 2 ^ 2 +
      C (q 8) * X 2 * X 3 + C (q 9) * X 3 ^ 2 := by
  simp [homogeneousAffineQuadrics, Fintype.linearCombination_apply,
    homogeneousAffineQuadricExponent, Fin.sum_univ_succ, smul_monomial, X,
    C_mul', pow_two, monomial_mul, ← Finsupp.single_add]
  abel

theorem homogeneousAffineQuadrics_tangent_eval (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (q : Fin 10 → K) (i : Fin 4) :
    aeval (tangentDualPoint U i) (homogeneousAffineQuadrics q) =
      ((![q 0, q 4, q 7, q 9] i,
        tangentQuadricEvaluation U ![q 1, q 2, q 3, q 5, q 6, q 8] i) : DualNumber K) := by
  fin_cases i <;> apply TrivSqZeroExt.ext <;>
    simp [homogeneousAffineQuadrics_expansion, tangentDualPoint,
      tangentQuadricEvaluation, TrivSqZeroExt.algebraMap_eq_inl,
      DualNumber.snd_mul, pow_two, hdiag] <;> ring

theorem offDiagonalQuadrics_tangent_eval (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (q : Fin 6 → K) (i : Fin 4) :
    aeval (tangentDualPoint U i) (offDiagonalQuadrics q) =
      TrivSqZeroExt.inr (tangentQuadricEvaluation U q i) := by
  rw [offDiagonalQuadrics, LinearMap.comp_apply]
  rw [homogeneousAffineQuadrics_tangent_eval U hdiag]
  fin_cases i <;> rfl

theorem offDiagonal_quadric_vanishing_iff (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (q : Fin 6 → K) :
    (∀ i, aeval (tangentDualPoint U i) (offDiagonalQuadrics q) = 0) ↔
      q ∈ LinearMap.ker (tangentQuadricEvaluationLinearMap U) := by
  constructor
  · intro h
    change tangentQuadricEvaluation U q = 0
    funext i
    have hi := congrArg TrivSqZeroExt.snd (h i)
    simpa [offDiagonalQuadrics_tangent_eval U hdiag q i] using hi
  · intro h i
    have hi := congrFun h i
    change tangentQuadricEvaluation U q i = 0 at hi
    rw [offDiagonalQuadrics_tangent_eval U hdiag q i, hi]
    simp

theorem homogeneous_quadric_is_offDiagonal (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (F : MvPolynomial (Fin 4) K)
    (hF : F.IsHomogeneous 2)
    (hvan : ∀ i : Fin 4, aeval (tangentDualPoint U i) F = 0) :
    ∃ q : Fin 6 → K, q ∈ LinearMap.ker (tangentQuadricEvaluationLinearMap U) ∧
      offDiagonalQuadrics q = F := by
  obtain ⟨a, ha⟩ := homogeneousAffineQuadrics_exhaustive F hF
  have hz (i : Fin 4) : ![a 0, a 4, a 7, a 9] i = 0 := by
    have h := congrArg TrivSqZeroExt.fst (show
      aeval (tangentDualPoint U i) (homogeneousAffineQuadrics a) = 0 by
        rw [ha]
        exact hvan i)
    rw [homogeneousAffineQuadrics_tangent_eval U hdiag] at h
    simpa using h
  let q : Fin 6 → K := ![a 1, a 2, a 3, a 5, a 6, a 8]
  have hqeq : offDiagonalQuadrics q = F := by
    rw [← ha]
    change homogeneousAffineQuadrics (offDiagonalCoefficientEmbedding q) =
      homogeneousAffineQuadrics a
    apply congrArg homogeneousAffineQuadrics
    funext i
    have h0 : a 0 = 0 := by simpa using hz 0
    have h4 : a 4 = 0 := by simpa using hz 1
    have h7 : a 7 = 0 := by simpa using hz 2
    have h9 : a 9 = 0 := by simpa using hz 3
    fin_cases i <;> simp [offDiagonalCoefficientEmbedding, q, h0, h4, h7, h9]
  refine ⟨q, ?_, hqeq⟩
  apply (offDiagonal_quadric_vanishing_iff U hdiag q).mp
  intro i
  rw [hqeq]
  exact hvan i

theorem offDiagonalQuadrics_mem_homogeneousTangentQuadrics (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (q : Fin 6 → K)
    (hq : q ∈ LinearMap.ker (tangentQuadricEvaluationLinearMap U)) :
    offDiagonalQuadrics q ∈ homogeneousTangentQuadrics U := by
  apply (mem_homogeneousTangentQuadrics U _).mpr
  exact ⟨offDiagonalQuadrics_homogeneous q,
    (offDiagonal_quadric_vanishing_iff U hdiag q).mpr hq⟩

noncomputable def offDiagonalToHomogeneousTangentQuadrics (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) :
    LinearMap.ker (tangentQuadricEvaluationLinearMap U) →ₗ[K]
      homogeneousTangentQuadrics U where
  toFun q := ⟨offDiagonalQuadrics q,
    offDiagonalQuadrics_mem_homogeneousTangentQuadrics U hdiag q q.property⟩
  map_add' q r := by
    apply Subtype.ext
    exact (offDiagonalQuadrics (K := K)).map_add q r
  map_smul' a q := by
    apply Subtype.ext
    exact (offDiagonalQuadrics (K := K)).map_smul a q

noncomputable def fullTangentQuadricEquiv (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) :
    LinearMap.ker (tangentQuadricEvaluationLinearMap U) ≃ₗ[K]
      homogeneousTangentQuadrics U :=
  LinearEquiv.ofBijective (offDiagonalToHomogeneousTangentQuadrics U hdiag)
    ⟨by
      intro q r h
      exact Subtype.ext (offDiagonalQuadrics_injective (congrArg Subtype.val h)),
    by
      intro F
      obtain ⟨q, hq, heq⟩ := homogeneous_quadric_is_offDiagonal U hdiag F.val
        ((mem_homogeneousTangentQuadrics U F.val).mp F.property).1
        ((mem_homogeneousTangentQuadrics U F.val).mp F.property).2
      exact ⟨⟨q, hq⟩, Subtype.ext heq⟩⟩

theorem fullTangentQuadric_finrank (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) :
    Module.finrank K (homogeneousTangentQuadrics U) =
      Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)) :=
  (fullTangentQuadricEquiv U hdiag).finrank_eq.symm

theorem three_le_tangentQuadric_kernel_of_homogeneous (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0)
    (hdim : 3 ≤ Module.finrank K (homogeneousTangentQuadrics U)) :
    3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)) := by
  rw [← fullTangentQuadric_finrank U hdiag]
  exact hdim

end QuarticNet
end PfaffianDescent
