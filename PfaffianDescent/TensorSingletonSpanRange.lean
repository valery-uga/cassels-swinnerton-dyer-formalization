import Mathlib.LinearAlgebra.TensorProduct.Quotient

/- SOURCE ONLY / UNVERIFIED. Exact tensor image of a cyclic submodule. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct
open scoped TensorProduct
universe u v w
variable {A : Type u} {L : Type v} {V : Type w} [CommRing A] [CommRing L] [Algebra A L]
  [AddCommGroup V] [Module A V]

theorem tensorSingletonSpanRange (v : V) :
    LinearMap.range (AlgebraTensorModule.lTensor L L
      (Submodule.span A ({v} : Set V)).subtype) =
      Submodule.span L ({(1 : L) ⊗ₜ[A] v} : Set (L ⊗[A] V)) := by
  apply le_antisymm
  · rintro y ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simpa using (Submodule.zero_mem
        (Submodule.span L ({(1 : L) ⊗ₜ[A] v} : Set (L ⊗[A] V))))
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul l w =>
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp w.property
      simp only [AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]
      rw [← ha, ← TensorProduct.smul_tmul]
      exact Submodule.mem_span_singleton.mpr
        ⟨a • l, by simp [TensorProduct.smul_tmul', smul_eq_mul]⟩
  · apply Submodule.span_le.mpr
    rintro y rfl
    exact ⟨(1 : L) ⊗ₜ[A]
      (⟨v, Submodule.mem_span_singleton_self v⟩ : Submodule.span A ({v} : Set V)),
      by simp⟩

end PfaffianDescent
