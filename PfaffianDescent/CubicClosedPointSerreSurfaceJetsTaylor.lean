import PfaffianDescent.CubicThreePointFirstJets
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
open MvPolynomial TrivSqZeroExt
namespace PfaffianDescent
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

/-- Literal polynomial evaluation on arbitrary square-zero first jets. -/
theorem cubicClosedPointSerreSurfaceJets_taylor
    {σ : Type*} [Fintype σ] (a : σ → K) (v : σ → Fin 2 → K)
    (p : MvPolynomial σ K) :
    aeval (fun j => inl (a j) + inr (v j)) p =
      inl (aeval a p) + inr (∑ j, (aeval a (pderiv j p)) • v j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    apply TrivSqZeroExt.ext <;>
      simp [map_add, Finset.sum_add_distrib, add_smul]
  | mul_X p k hp =>
    rw [map_mul, hp, aeval_X]
    apply TrivSqZeroExt.ext
    · simp
    · simp [pderiv_mul, pderiv_X, Pi.single_apply, apply_ite, Finset.sum_add_distrib,
        add_smul, mul_smul, Finset.smul_sum, mul_comm, add_comm]
      have hite (x : σ) :
          (if k = x then (eval a p) • v x + a k • (eval a (pderiv x p)) • v x
            else a k • (eval a (pderiv x p)) • v x) =
          (if k = x then (eval a p) • v x else 0) +
            a k • (eval a (pderiv x p)) • v x := by
        split_ifs <;> simp
      simp_rw [hite]
      simp [Finset.sum_add_distrib]

end PfaffianDescent
