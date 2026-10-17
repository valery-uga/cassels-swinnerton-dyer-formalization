import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.Range
import Lean.Elab.Tactic.Omega

/-! Independent ordinary finite exact-rank algebra. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray

/-- The full first-map image is retained in a finite exact rank comparison. -/
theorem normalization_finiteExact_rank_correction
    {K A B C D : Type*} [Field K]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module K A] [Module K B] [Module K C] [Module K D]
    [Module.Finite K B] [Module.Finite K C]
    (σ : A →ₗ[K] B) (δ : B →ₗ[K] C) (g : C →ₗ[K] D)
    (hσδ : Function.Exact σ δ) (hδg : Function.Exact δ g)
    (hg : Function.Surjective g) :
    Module.finrank K C + Module.finrank K (LinearMap.range σ) =
      Module.finrank K D + Module.finrank K B := by
  letI : Module.Finite K D := Module.Finite.of_surjective g hg
  have hG := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hδg.linearMap_ker_eq] at hG
  have hδ := δ.finrank_range_add_finrank_ker
  rw [hσδ.linearMap_ker_eq] at hδ
  omega

/-- Both full constants ranks are retained; only the SAME image rank cancels. -/
theorem normalization_fullConstants_euler_of_rank_correction
    (rC rN hC hN s q : ℕ) (h0 : rN = rC + s) (h1 : hC + s = hN + q) :
    (rN : ℤ) - (hN : ℤ) = (rC : ℤ) - (hC : ℤ) + (q : ℤ) := by
  omega

end PfaffianDescent.Coray
