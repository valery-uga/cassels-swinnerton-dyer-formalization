import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Kernel dimensions and bases after an injective scalar extension. -/

noncomputable section
namespace PfaffianDescent

open Module

universe u

theorem cubicKernelFamily_card_le_finrank
    {E V W : Type u} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] [AddCommGroup W] [Module E W]
    (T : V →ₗ[E] W) {n : ℕ} (q : Fin n → V)
    (hli : LinearIndependent E q) (hmem : ∀ i, q i ∈ T.ker) :
    n ≤ finrank E T.ker := by
  have hliH : LinearIndependent E (fun i : Fin n => (⟨q i, hmem i⟩ : T.ker)) := by
    apply LinearIndependent.of_comp T.ker.subtype
    exact hli
  simpa only [Fintype.card_fin] using hliH.fintype_card_le_finrank

theorem cubicKernelFamily_span_eq_kernel
    {E V W : Type u} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] [AddCommGroup W] [Module E W]
    (T : V →ₗ[E] W) {n : ℕ} (q : Fin n → V)
    (hli : LinearIndependent E q) (hmem : ∀ i, q i ∈ T.ker)
    (hdim : finrank E T.ker = n) :
    Submodule.span E (Set.range q) = T.ker := by
  have hliH : LinearIndependent E (fun i : Fin n => (⟨q i, hmem i⟩ : T.ker)) := by
    apply LinearIndependent.of_comp T.ker.subtype
    exact hli
  have hcard : Fintype.card (Fin n) = finrank E T.ker := by
    simpa only [Fintype.card_fin] using hdim.symm
  have hspan := hliH.span_eq_top_of_card_eq_finrank' hcard
  exact (Submodule.span_range_subtype_eq_top_iff T.ker hmem).mp hspan

theorem cubicGroundKernel_finrank_of_independent_extension
    {F E V U A B : Type u} [Field F] [Field E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    [AddCommGroup B] [Module E B]
    (R : V →ₗ[F] A) (T : U →ₗ[E] B) (f : V → U) (n d : ℕ)
    (hV : finrank F V = n + d) (hA : finrank F A ≤ n)
    (hT : finrank E T.ker = d)
    (hli : ∀ m (q : Fin m → V), LinearIndependent F q →
      LinearIndependent E (fun i => f (q i)))
    (hmem : ∀ q, R q = 0 → T (f q) = 0) :
    finrank F R.ker = d := by
  classical
  have hdim := R.finrank_range_add_finrank_ker
  have hrange : finrank F R.range ≤ finrank F A := Submodule.finrank_le R.range
  have hlow : d ≤ finrank F R.ker := by omega
  let C : Basis (Fin (finrank F R.ker)) F R.ker := Module.finBasis F R.ker
  let q : Fin (finrank F R.ker) → V := fun i => (C i).1
  have hq : LinearIndependent F q :=
    C.linearIndependent.map' R.ker.subtype (Submodule.ker_subtype R.ker)
  have hqmem : ∀ i, f (q i) ∈ T.ker := by
    intro i
    exact LinearMap.mem_ker.mpr (hmem (q i) (C i).property)
  have hhigh := cubicKernelFamily_card_le_finrank T
    (fun i => f (q i)) (hli _ q hq) hqmem
  rw [hT] at hhigh
  omega

theorem cubicGroundKernel_basis_spans_extended_kernel
    {F E V U A B : Type u} [Field F] [Field E]
    [AddCommGroup V] [Module F V]
    [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module E B]
    (R : V →ₗ[F] A) (T : U →ₗ[E] B) (f : V → U) (d : ℕ)
    (hT : finrank E T.ker = d)
    (hli : ∀ m (q : Fin m → V), LinearIndependent F q →
      LinearIndependent E (fun i => f (q i)))
    (hmem : ∀ q, R q = 0 → T (f q) = 0)
    (C : Basis (Fin d) F R.ker) :
    Submodule.span E (Set.range (fun i => f (C i).1)) = T.ker := by
  let q : Fin d → V := fun i => (C i).1
  have hq : LinearIndependent F q :=
    C.linearIndependent.map' R.ker.subtype (Submodule.ker_subtype R.ker)
  have hqmem : ∀ i, f (q i) ∈ T.ker := by
    intro i
    exact LinearMap.mem_ker.mpr (hmem (q i) (C i).property)
  exact cubicKernelFamily_span_eq_kernel T (fun i => f (q i))
    (hli _ q hq) hqmem hT

end PfaffianDescent
