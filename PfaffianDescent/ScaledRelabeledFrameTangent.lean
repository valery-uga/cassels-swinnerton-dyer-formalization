import PfaffianDescent.SuppliedFrameTangentWeights
import Mathlib.LinearAlgebra.Basis.SMul

/-! SOURCE ONLY, UNVERIFIED. Exact basis-coordinate law, including arbitrary
radial additions that disappear after projective diagonal normalization. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def scaledRelabeledFrame (b : Basis (Fin 4) K V)
    (rho : Equiv.Perm (Fin 4)) (c : Fin 4 → Kˣ) : Basis (Fin 4) K V :=
  (b.reindex rho.symm).unitsSMul c

def frameNormalizedTangent (b : Basis (Fin 4) K V) (x : Fin 4 → V) :
    Fin 4 → Fin 4 → K := fun i j => if i = j then 0 else b.repr (x i) j

theorem scaledRelabeledFrame_column (b : Basis (Fin 4) K V)
    (rho : Equiv.Perm (Fin 4)) (c : Fin 4 → Kˣ) (i : Fin 4) :
    scaledRelabeledFrame b rho c i = (c i : K) • b (rho i) := by
  simp only [scaledRelabeledFrame, Basis.unitsSMul_apply, Basis.reindex_apply,
    Equiv.symm_symm, Units.smul_def]

/-- An epsilon reparameterization and a radial vector change have their
actual coordinate effect computed in the supplied ambient frame. -/
theorem frameNormalizedTangent_scaledRelabeledFrame
    (b : Basis (Fin 4) K V) (rho : Equiv.Perm (Fin 4))
    (c : Fin 4 → Kˣ) (epsilon radial : Fin 4 → K) (x : Fin 4 → V) :
    frameNormalizedTangent (scaledRelabeledFrame b rho c)
      (fun i => (epsilon i * (c i : K)) • x (rho i) +
        radial i • scaledRelabeledFrame b rho c i) =
      suppliedFrameTangent (frameNormalizedTangent b x) rho
        (fun i => (c i : K)) epsilon := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [frameNormalizedTangent, suppliedFrameTangent]
  · have hrho : rho i ≠ rho j := fun h => hij (rho.injective h)
    simp only [frameNormalizedTangent, hij, hrho, if_false, map_add,
      map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Basis.repr_self_apply, suppliedFrameTangent]
    simp only [hij, if_false, mul_zero, add_zero]
    simp only [scaledRelabeledFrame, Basis.repr_unitsSMul,
      Basis.repr_reindex_apply, Equiv.symm_symm, Units.smul_def,
      smul_eq_mul, Units.val_inv_eq_inv_val]
    rw [div_eq_mul_inv]
    ring

end PfaffianDescent.QuarticNet
