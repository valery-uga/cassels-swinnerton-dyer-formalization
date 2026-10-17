import PfaffianDescent.QuarticTraceDuality
import Mathlib.Algebra.DualNumber

/-!
# The square-zero algebra in the length-eight tangent construction

This is the algebraic quotient underlying the first-order length-eight
subscheme in Proposition 4.3 of `2-proofs.tex`.
-/

namespace PfaffianDescent
namespace QuarticNet

open Module LinearMap TrivSqZeroExt

section
variable {L E : Type*} [Field L] [AddCommGroup E]
  [Module L E] [Module Lᵐᵒᵖ E] [IsCentralScalar L E]

/-- A surjective tangent quotient induces a surjection of square-zero
extensions. -/
theorem squareZero_map_surjective (q : E →ₗ[L] L) (hq : Function.Surjective q) :
    Function.Surjective (TrivSqZeroExt.map q) := by
  intro x
  obtain ⟨e, he⟩ := hq x.snd
  refine ⟨TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr e, ?_⟩
  apply TrivSqZeroExt.ext <;> simp [he]

/-- The quotient by the kernel of the square-zero map is the dual-number
algebra over the residue field. -/
noncomputable def squareZeroQuotientEquiv (q : E →ₗ[L] L) (hq : Function.Surjective q) :
    (TrivSqZeroExt L E ⧸ RingHom.ker (TrivSqZeroExt.map q)) ≃ₐ[L] DualNumber L :=
  Ideal.quotientKerAlgEquivOfSurjective (squareZero_map_surjective q hq)

theorem squareZero_quotient_finrank (q : E →ₗ[L] L) (hq : Function.Surjective q) :
    Module.finrank L (TrivSqZeroExt L E ⧸ RingHom.ker (TrivSqZeroExt.map q)) = 2 := by
  rw [(squareZeroQuotientEquiv q hq).toLinearEquiv.finrank_eq]
  change Module.finrank L (L × L) = 2
  simp [Module.finrank_prod]

end

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A nonzero trace functional on a separable degree-four extension has a
three-dimensional kernel. -/
theorem trace_ker_finrank_three (hdim : Module.finrank K L = 4) :
    Module.finrank K (LinearMap.ker (Algebra.trace K L)) = 3 := by
  have hsurj : Function.Surjective (Algebra.trace K L) := by
    obtain ⟨x, hx⟩ := Algebra.trace_surjective K L 1
    intro y
    exact ⟨y • x, by simpa [map_smul, hx]⟩
  have htop : LinearMap.range (Algebra.trace K L) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hsum := (Algebra.trace K L).finrank_range_add_finrank_ker
  rw [htop, finrank_top, hdim] at hsum
  simp at hsum
  omega

/-- The trace-annihilating quotient has at least a three-dimensional kernel
on the six-dimensional quadric parameter space. -/
theorem exists_surjective_quotient_with_three_dimensional_kernel
    (hdim : Module.finrank K L = 4)
    (φ : (Fin 6 → K) →ₗ[K] (Fin 2 → L)) :
    ∃ q : (Fin 2 → L) →ₗ[L] L, Function.Surjective q ∧
      3 ≤ Module.finrank K (LinearMap.ker ((q.restrictScalars K).comp φ)) := by
  obtain ⟨q, hq, htrace⟩ :=
    exists_surjective_trace_quotient_annihilating_six_to_two hdim φ
  let g : (Fin 6 → K) →ₗ[K] L := (q.restrictScalars K).comp φ
  have hrange : LinearMap.range g ≤ LinearMap.ker (Algebra.trace K L) := by
    rintro y ⟨x, rfl⟩
    exact htrace x
  have hgrange : Module.finrank K (LinearMap.range g) ≤ 3 := by
    rw [← trace_ker_finrank_three hdim]
    exact Submodule.finrank_mono hrange
  have hsum := g.finrank_range_add_finrank_ker
  rw [show Module.finrank K (Fin 6 → K) = 6 by simp] at hsum
  refine ⟨q, hq, ?_⟩
  change 3 ≤ finrank K (LinearMap.ker g)
  omega

/-- The square-zero quotient selected by the trace construction has dimension
eight over the ground field. -/
theorem squareZero_quotient_ground_finrank_eight
    (hdim : Module.finrank K L = 4) (q : (Fin 2 → L) →ₗ[L] L)
    (hq : Function.Surjective q) :
    Module.finrank K (TrivSqZeroExt L (Fin 2 → L) ⧸
      RingHom.ker (TrivSqZeroExt.map q)) = 8 := by
  rw [((squareZeroQuotientEquiv q hq).toLinearEquiv.restrictScalars K).finrank_eq]
  change Module.finrank K (L × L) = 8
  simp [Module.finrank_prod, hdim]

/-- The algebraic first-order construction required in Proposition 4.3:
there is a square-zero quotient of ground-field rank eight for which at
least three independent quadric parameters vanish. -/
theorem exists_squareZero_quotient_with_three_dimensional_kernel
    (hdim : Module.finrank K L = 4)
    (φ : (Fin 6 → K) →ₗ[K] (Fin 2 → L)) :
    ∃ q : (Fin 2 → L) →ₗ[L] L, Function.Surjective q ∧
      Module.finrank K (TrivSqZeroExt L (Fin 2 → L) ⧸
        RingHom.ker (TrivSqZeroExt.map q)) = 8 ∧
      3 ≤ Module.finrank K (LinearMap.ker ((q.restrictScalars K).comp φ)) := by
  obtain ⟨q, hq, hker⟩ := exists_surjective_quotient_with_three_dimensional_kernel hdim φ
  exact ⟨q, hq, squareZero_quotient_ground_finrank_eight hdim q hq, hker⟩

end
end QuarticNet
end PfaffianDescent
