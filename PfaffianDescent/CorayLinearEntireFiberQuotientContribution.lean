import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Lean.Elab.Tactic.Omega

/-! Canonical actual quotient map for a linear residue/fibre square.
Source finiteness is not assumed for the cardinal-rank contribution. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u
variable {K R B L C : Type u} [Field K]
  [AddCommGroup R] [AddCommGroup B] [AddCommGroup L] [AddCommGroup C]
  [Module K R] [Module K B] [Module K L] [Module K C]
set_option autoImplicit false

/-- The canonical map of the ACTUAL image quotients. Its underlying map is
beta, with image containment derived from the genuine linear square. -/
def linearResidueFiberDiagramQuotientMap001
    (sigma : R →ₗ[K] B) (alpha : R →ₗ[K] L) (j : L →ₗ[K] C) (beta : B →ₗ[K] C)
    (hSquare : beta.comp sigma = j.comp alpha) :
    (B ⧸ LinearMap.range sigma) →ₗ[K] (C ⧸ LinearMap.range j) :=
  (LinearMap.range sigma).mapQ (LinearMap.range j) beta (by
    intro b hb
    obtain ⟨r, hr⟩ := hb
    refine ⟨alpha r, ?_⟩
    have h := LinearMap.congr_fun hSquare r
    change beta (sigma r) = j (alpha r) at h
    exact h.symm.trans (congrArg beta hr))

/-- Surjectivity on the ENTIRE fibre descends to the canonical quotient;
no injectivity or source finiteness is needed. -/
theorem linearResidueFiberDiagramQuotientMap_surjective001
    (sigma : R →ₗ[K] B) (alpha : R →ₗ[K] L) (j : L →ₗ[K] C) (beta : B →ₗ[K] C)
    (hSquare : beta.comp sigma = j.comp alpha) (hBeta : Function.Surjective beta) :
    Function.Surjective (linearResidueFiberDiagramQuotientMap001 sigma alpha j beta hSquare) := by
  intro y
  obtain ⟨c, rfl⟩ := (LinearMap.range j).mkQ_surjective y
  obtain ⟨b, rfl⟩ := hBeta c
  exact ⟨(LinearMap.range sigma).mkQ b, rfl⟩

/-- An injective residue field of ground dimension d in the full finite
fibre of ground dimension d*s gives the exact target quotient rank d*(s-1).
The actual gluing source has at least that CARDINAL rank, even before its
finiteness is constructed. The natural finrank statement follows only once
that separate finite-source fact has been genuinely supplied. -/
theorem linearResidueFiberDiagram_quotient_target_finrank_and_source_rank001
    [Module.Finite K L] [Module.Finite K C]
    (sigma : R →ₗ[K] B) (alpha : R →ₗ[K] L) (j : L →ₗ[K] C) (beta : B →ₗ[K] C)
    (hSquare : beta.comp sigma = j.comp alpha) (hBeta : Function.Surjective beta)
    (hJ : Function.Injective j) (d s : ℕ)
    (hL : Module.finrank K L = d) (hC : Module.finrank K C = d * s) :
    Module.finrank K (C ⧸ LinearMap.range j) = d * (s - 1) ∧
      ((d * (s - 1) : ℕ) : Cardinal.{u}) ≤ Module.rank K (B ⧸ LinearMap.range sigma) ∧
      (∀ hFinite : Module.Finite K (B ⧸ LinearMap.range sigma),
        letI := hFinite
        d * (s - 1) ≤ Module.finrank K (B ⧸ LinearMap.range sigma)) := by
  let q := linearResidueFiberDiagramQuotientMap001 sigma alpha j beta hSquare
  have hSurjective : Function.Surjective q :=
    linearResidueFiberDiagramQuotientMap_surjective001 sigma alpha j beta hSquare hBeta
  have hImage : Module.finrank K (LinearMap.range j) = Module.finrank K L :=
    LinearMap.finrank_range_of_inj hJ
  have hTotal := (LinearMap.range j).finrank_quotient_add_finrank
  have hTarget : Module.finrank K (C ⧸ LinearMap.range j) = d * (s - 1) := by
    rw [hImage, hL, hC] at hTotal
    have hSubtract : d * (s - 1) = d * s - d := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  refine ⟨hTarget, ?_, ?_⟩
  · calc
      ((d * (s - 1) : ℕ) : Cardinal.{u}) =
          (Module.finrank K (C ⧸ LinearMap.range j) : Cardinal.{u}) := congrArg Nat.cast hTarget.symm
      _ = Module.rank K (C ⧸ LinearMap.range j) := by rw [Module.finrank_eq_rank]
      _ ≤ Module.rank K (B ⧸ LinearMap.range sigma) := q.rank_le_of_surjective hSurjective
  · intro hFinite
    letI := hFinite
    have h := LinearMap.finrank_le_finrank_of_surjective (f := q) hSurjective
    exact hTarget.symm.le.trans h

end PfaffianDescent.Coray
