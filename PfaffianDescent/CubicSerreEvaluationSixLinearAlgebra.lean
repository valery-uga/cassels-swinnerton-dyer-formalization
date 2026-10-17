import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Six actual point-fibre dimensions and a full derivative span prove
surjectivity of actual section evaluation; no comparison isomorphism is assumed. -/

noncomputable section
namespace PfaffianDescent
open Module
universe u

theorem cubicSerreEvaluationSix_surjective_of_derivative_span
    {E U V : Type u} [Field E] [AddCommGroup U] [Module E U]
    [AddCommGroup V] [Module E V]
    (A : U →ₗ[E] V) (D : V →ₗ[E] (Fin 3 → Fin 2 → E))
    (hV : finrank E V = 6)
    (w : Fin 9 → Fin 3 → Fin 2 → E)
    (hspan : Submodule.span E (Set.range w) = ⊤)
    (hw : ∀ k, w k ∈ (D.comp A).range) :
    Function.Surjective A ∧ Function.Bijective D := by
  have hle : ⊤ ≤ (D.comp A).range := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hw k
  have hDA : Function.Surjective (D.comp A) :=
    LinearMap.range_eq_top.mp (top_unique hle)
  have hD : Function.Surjective D := by
    intro z
    obtain ⟨s, hs⟩ := hDA z
    exact ⟨A s, hs⟩
  letI : Module.Finite E V := Module.finite_of_finrank_pos (by rw [hV]; decide)
  have hdim : finrank E V = finrank E (Fin 3 → Fin 2 → E) := by
    rw [hV]
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]
  have hDi : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hD
  refine ⟨?_, hDi, hD⟩
  intro z
  obtain ⟨s, hs⟩ := hDA (D z)
  exact ⟨s, hDi hs⟩

theorem cubicSerreEvaluationSix_surjective_of_globalDerivativeWitnesses
    {F E M V : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup M] [Module F M] [AddCommGroup V] [Module E V]
    (A : TensorProduct F E M →ₗ[E] V)
    (D : V →ₗ[E] (Fin 3 → Fin 2 → E))
    (hV : finrank E V = 6)
    (w : Fin 9 → Fin 3 → Fin 2 → E)
    (hspan : Submodule.span E (Set.range w) = ⊤)
    (hw : ∀ k, ∃ s : M, D (A (TensorProduct.tmul F (1 : E) s)) = w k) :
    Function.Surjective A ∧ Function.Bijective D := by
  apply cubicSerreEvaluationSix_surjective_of_derivative_span A D hV w hspan
  intro k
  obtain ⟨s, hs⟩ := hw k
  exact ⟨TensorProduct.tmul F (1 : E) s, hs⟩

end PfaffianDescent
