import PfaffianDescent.QuarticExceptionalResidual
import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.QuarticTangentRescaling

/-!
# Exceptional parametrization at a tangent double point

The explicit exceptional twisted-cubic parametrization contains the first
normalized tangent double point.  This is the local calculation needed to
connect the geometric tangent-net construction to the residual argument.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial

variable {K : Type*} [Field K]

theorem exceptional_param_tangent_zero
    (a b c d e f : K)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : aeval (tangentDualPoint (skewTangentDirections a b c d e f) 0) F = 0) :
    aeval ![(1 : DualNumber K), TrivSqZeroExt.inr a]
      (exceptionalTwistedCubicParam a b c d e F) = 0 := by
  rw [exceptionalTwistedCubicParam_eval]
  let u : DualNumber K :=
    TrivSqZeroExt.inl (a * d * e) + TrivSqZeroExt.inr (-a * a * (d * c + b * e))
  have hpoint : linearImageCubicVeronese (baseLocusCubicCoefficientMatrix a b c d e)
      (1 : DualNumber K) (TrivSqZeroExt.inr a) =
      u • tangentDualPoint (skewTangentDirections a b c d e f) 0 := by
    funext i
    fin_cases i <;>
      apply TrivSqZeroExt.ext <;>
      simp [linearImageCubicVeronese, cubicVeronese, baseLocusCubicCoefficientMatrix,
        tangentDualPoint, skewTangentDirections, u, Fin.sum_univ_four,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul] <;> ring
  rw [hpoint, aeval_smul_of_homogeneous F 3 hF, hvan, mul_zero]

theorem exceptional_param_tangent_one
    (a b c d e f : K)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : aeval (tangentDualPoint (skewTangentDirections a b c d e f) 1) F = 0) :
    aeval ![TrivSqZeroExt.inr (-a), (1 : DualNumber K)]
      (exceptionalTwistedCubicParam a b c d e F) = 0 := by
  rw [exceptionalTwistedCubicParam_eval]
  let u : DualNumber K :=
    TrivSqZeroExt.inl (a * b * c) + TrivSqZeroExt.inr (a * a * (d * c + b * e))
  have hpoint : linearImageCubicVeronese (baseLocusCubicCoefficientMatrix a b c d e)
      (TrivSqZeroExt.inr (-a)) (1 : DualNumber K) =
      u • tangentDualPoint (skewTangentDirections a b c d e f) 1 := by
    funext i
    fin_cases i <;>
      apply TrivSqZeroExt.ext <;>
      simp [linearImageCubicVeronese, cubicVeronese, baseLocusCubicCoefficientMatrix,
        tangentDualPoint, skewTangentDirections, u, Fin.sum_univ_four,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul] <;> ring
  rw [hpoint, aeval_smul_of_homogeneous F 3 hF, hvan, mul_zero]

theorem exceptional_param_tangent_two
    (a b c d e f : K) (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    aeval ![TrivSqZeroExt.inl b + TrivSqZeroExt.inr (-b * b * d),
      TrivSqZeroExt.inl d] (exceptionalTwistedCubicParam a b c d e F) = 0 := by
  rw [exceptionalTwistedCubicParam_eval]
  let l : Fin 4 → K := ![1, 1, a, 1]
  have hv := rescaleTangentDirections_vanishing (skewTangentDirections a b c d e f) l F hvan
  let u : DualNumber K :=
    TrivSqZeroExt.inl (b * b * d * d * (b * e - c * d)) +
      TrivSqZeroExt.inr (-b ^ 3 * d ^ 3 * ((b * e - c * d) + b * e))
  have hpoint : linearImageCubicVeronese (baseLocusCubicCoefficientMatrix a b c d e)
      (TrivSqZeroExt.inl b + TrivSqZeroExt.inr (-b * b * d))
      (TrivSqZeroExt.inl d) =
      u • tangentDualPoint (rescaleTangentDirections l
        (skewTangentDirections a b c d e f)) 2 := by
    funext i
    fin_cases i <;>
      apply TrivSqZeroExt.ext <;>
      simp [linearImageCubicVeronese, cubicVeronese, baseLocusCubicCoefficientMatrix,
        tangentDualPoint, rescaleTangentDirections, skewTangentDirections, l, u,
        Fin.sum_univ_four, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul] <;> try ring
    · dsimp [baseLocusDelta] at hdelta
      linear_combination -b ^ 2 * d ^ 2 * hdelta
  rw [hpoint, aeval_smul_of_homogeneous F 3 hF, hv 2, mul_zero]

theorem exceptional_param_tangent_three
    (a b c d e f : K) (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    aeval ![TrivSqZeroExt.inl c + TrivSqZeroExt.inr (-c * c * e),
      TrivSqZeroExt.inl e] (exceptionalTwistedCubicParam a b c d e F) = 0 := by
  rw [exceptionalTwistedCubicParam_eval]
  let l : Fin 4 → K := ![1, 1, 1, a]
  have hv := rescaleTangentDirections_vanishing (skewTangentDirections a b c d e f) l F hvan
  let u : DualNumber K :=
    TrivSqZeroExt.inl (c * c * e * e * (c * d - b * e)) +
      TrivSqZeroExt.inr (c ^ 3 * e ^ 3 * (b * e - 2 * c * d))
  have hpoint : linearImageCubicVeronese (baseLocusCubicCoefficientMatrix a b c d e)
      (TrivSqZeroExt.inl c + TrivSqZeroExt.inr (-c * c * e))
      (TrivSqZeroExt.inl e) =
      u • tangentDualPoint (rescaleTangentDirections l
        (skewTangentDirections a b c d e f)) 3 := by
    funext i
    fin_cases i <;>
      apply TrivSqZeroExt.ext <;>
      simp [linearImageCubicVeronese, cubicVeronese, baseLocusCubicCoefficientMatrix,
        tangentDualPoint, rescaleTangentDirections, skewTangentDirections, l, u,
        Fin.sum_univ_four, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul] <;> try ring
    · dsimp [baseLocusDelta] at hdelta
      linear_combination -c ^ 2 * e ^ 2 * hdelta
  rw [hpoint, aeval_smul_of_homogeneous F 3 hF, hv 3, mul_zero]

/-- In the exceptional branch the explicit binary-cubic parametrization
contains all four normalized tangent double points of the net. -/
theorem exceptional_param_contains_normalized_tangent_net
    (a b c d e f : K) (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    aeval ![(1 : DualNumber K), TrivSqZeroExt.inr a]
        (exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      aeval ![TrivSqZeroExt.inr (-a), (1 : DualNumber K)]
        (exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      aeval ![TrivSqZeroExt.inl b + TrivSqZeroExt.inr (-b * b * d),
        TrivSqZeroExt.inl d] (exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      aeval ![TrivSqZeroExt.inl c + TrivSqZeroExt.inr (-c * c * e),
        TrivSqZeroExt.inl e] (exceptionalTwistedCubicParam a b c d e F) = 0 := by
  exact ⟨exceptional_param_tangent_zero a b c d e f F hF (hvan 0),
    exceptional_param_tangent_one a b c d e f F hF (hvan 1),
    exceptional_param_tangent_two a b c d e f hdelta F hF hvan,
    exceptional_param_tangent_three a b c d e f hdelta F hF hvan⟩

end QuarticNet
end PfaffianDescent
