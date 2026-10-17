import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases

namespace PfaffianDescent
section
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The operator with eigenvalues one, two, and three on the three blocks. -/
def goodSpectralOperator : (Fin 3 → M) →ₗ[R] (Fin 3 → M) where
  toFun x := ![x 0, (2 : R) • x 1, (3 : R) • x 2]
  map_add' x y := by ext i; fin_cases i <;> simp [smul_add]
  map_smul' c x := by ext i; fin_cases i <;> simp [smul_smul, mul_comm]

/-- Projection to a single eigenspace block. -/
def goodBlockProjection (i : Fin 3) : (Fin 3 → M) →ₗ[R] (Fin 3 → M) :=
  (LinearMap.single R (fun _ : Fin 3 => M) i).comp (LinearMap.proj i)

lemma goodBlockProjection_apply (i : Fin 3) (x : Fin 3 → M) :
    goodBlockProjection R M i x = Pi.single i (x i) := rfl

/-- Integral polynomial identities for the spectral projectors. Only two must be inverted. -/
lemma goodBlockProjection_zero_polynomial (x : Fin 3 → M) :
    (2 : R) • goodBlockProjection R M 0 x =
      goodSpectralOperator R M (goodSpectralOperator R M x) -
        (5 : R) • goodSpectralOperator R M x + (6 : R) • x := by
  ext i
  fin_cases i <;> simp [goodBlockProjection_apply, goodSpectralOperator] <;> module

lemma goodBlockProjection_one_polynomial (x : Fin 3 → M) :
    goodBlockProjection R M 1 x =
      -(goodSpectralOperator R M (goodSpectralOperator R M x)) +
        (4 : R) • goodSpectralOperator R M x - (3 : R) • x := by
  ext i
  fin_cases i <;> simp [goodBlockProjection_apply, goodSpectralOperator] <;> module

lemma goodBlockProjection_two_polynomial (x : Fin 3 → M) :
    (2 : R) • goodBlockProjection R M 2 x =
      goodSpectralOperator R M (goodSpectralOperator R M x) -
        (3 : R) • goodSpectralOperator R M x + (2 : R) • x := by
  ext i
  fin_cases i <;> simp [goodBlockProjection_apply, goodSpectralOperator] <;> module

lemma goodBlockProjection_sum (x : Fin 3 → M) :
    ∑ i, goodBlockProjection R M i x = x := by
  ext i
  simp [goodBlockProjection_apply]

lemma goodBlockProjection_comp (i j : Fin 3) (x : Fin 3 → M) :
    goodBlockProjection R M i (goodBlockProjection R M j x) =
      if i = j then goodBlockProjection R M i x else 0 := by
  by_cases h : i = j
  · subst j; simp [goodBlockProjection_apply]
  · simp [goodBlockProjection_apply, h]

/-- An invariant submodule is preserved by every spectral projector over any base ring
in which two is a unit. This includes nonreduced coefficient rings. -/
theorem goodBlockProjection_mem (h2 : IsUnit (2 : R))
    (W : Submodule R (Fin 3 → M))
    (hW : ∀ x ∈ W, goodSpectralOperator R M x ∈ W)
    (i : Fin 3) {x : Fin 3 → M} (hx : x ∈ W) :
    goodBlockProjection R M i x ∈ W := by
  have hTx := hW x hx
  have hTTx := hW _ hTx
  fin_cases i
  · apply (W.smul_mem_iff_of_isUnit h2).mp
    change (2 : R) • goodBlockProjection R M 0 x ∈ W
    rw [goodBlockProjection_zero_polynomial R M x]
    exact W.add_mem (W.sub_mem hTTx (W.smul_mem _ hTx)) (W.smul_mem _ hx)
  · change goodBlockProjection R M 1 x ∈ W
    rw [goodBlockProjection_one_polynomial R M x]
    exact W.sub_mem (W.add_mem (W.neg_mem hTTx) (W.smul_mem _ hTx)) (W.smul_mem _ hx)
  · apply (W.smul_mem_iff_of_isUnit h2).mp
    change (2 : R) • goodBlockProjection R M 2 x ∈ W
    rw [goodBlockProjection_two_polynomial R M x]
    exact W.add_mem (W.sub_mem hTTx (W.smul_mem _ hTx)) (W.smul_mem _ hx)

/-- The submodule lying in an individual two-dimensional block. -/
def goodBlockSubmodule (W : Submodule R (Fin 3 → M)) (i : Fin 3) : Submodule R M :=
  W.comap (LinearMap.single R (fun _ : Fin 3 => M) i)

/-- The spectral splitting of invariant submodules, with an explicit inverse.
It is valid over arbitrary coefficient rings, without a reducedness assumption. -/
def goodSpectralSplitting (h2 : IsUnit (2 : R))
    (W : Submodule R (Fin 3 → M))
    (hW : ∀ x ∈ W, goodSpectralOperator R M x ∈ W) :
    W ≃ₗ[R] ((i : Fin 3) → goodBlockSubmodule R M W i) where
  toFun x i := ⟨x.1 i, goodBlockProjection_mem R M h2 W hW i x.2⟩
  invFun x := ⟨fun i => (x i).1, by
    rw [← goodBlockProjection_sum R M (fun i => (x i).1)]
    exact W.sum_mem (fun i _ => (x i).2)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

end
end PfaffianDescent
