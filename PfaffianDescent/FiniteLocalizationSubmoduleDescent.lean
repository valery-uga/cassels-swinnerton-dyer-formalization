import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] (a : ι → R)
  (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  [∀ i, IsLocalization.Away (a i) (S i)]
  (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, Module (S i) (N i)] [∀ i, IsScalarTower R (S i) (N i)]
  (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule.Away (a i) (f i)]
  (W : ∀ i, Submodule (S i) (N i))

/-- The submodule of ambient vectors satisfying all local submodule conditions. -/
def finiteLocalizationSubmodule : Submodule R M :=
  ⨅ i, ((W i).restrictScalars R).comap (f i)

lemma mem_finiteLocalizationSubmodule (x : M) :
    x ∈ finiteLocalizationSubmodule S N f W ↔ ∀ i, f i x ∈ W i := by
  simp only [finiteLocalizationSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.restrictScalars_mem]

/-- Compatible local submodules descend: denominator clearing is uniform because the family is finite. -/
theorem finiteLocalizationSubmodule_localized
    (hcompat : ∀ i j x, f i x ∈ W i → ∃ e : ℕ, (a i ^ e) • f j x ∈ W j) (i : ι) :
    (finiteLocalizationSubmodule S N f W).localized' (S i) (.powers (a i)) (f i) = W i := by
  classical
  apply le_antisymm
  · rw [Submodule.localized'_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_finiteLocalizationSubmodule S N f W x).mp hx i
  · intro y hy
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (.powers (a i)) (f i) y
    have hx : f i x ∈ W i := by
      rw [← IsLocalizedModule.mk'_cancel' (f i) x s]
      exact (W i).smul_of_tower_mem s hy
    choose e he using fun j => hcompat i j x hx
    let d := Finset.univ.sup e
    have hd (j : ι) : e j ≤ d := Finset.le_sup (Finset.mem_univ j)
    have hw : (a i ^ d) • x ∈ finiteLocalizationSubmodule S N f W := by
      rw [mem_finiteLocalizationSubmodule]
      intro j
      rw [map_smul, ← Nat.sub_add_cancel (hd j), pow_add, mul_smul]
      exact (W j).smul_of_tower_mem (a i ^ (d - e j)) (he j)
    refine ⟨(a i ^ d) • x, hw, ⟨a i ^ d, ⟨d, rfl⟩⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left (S := .powers (a i)) (f i) x ⟨a i ^ d, ⟨d, rfl⟩⟩ s

end
end PfaffianDescent
