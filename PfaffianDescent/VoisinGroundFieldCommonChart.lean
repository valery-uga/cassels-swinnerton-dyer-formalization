import PfaffianDescent.VoisinProjectiveVectorSchemePoint
import Mathlib.Algebra.Module.Submodule.Union

/-!
A common projective chart for finitely many extension-field points can
be chosen with coefficients in the original infinite ground field.
The extension need not be finite.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

/-- Each nonzero extension-field vector excludes one proper ground-field
linear subspace of coefficient vectors. -/
theorem exists_groundField_dotProduct_nonzero
    {K : Type u} [Field K] [Infinite K]
    {L : Type v} [Field L] [Algebra K L]
    {ι σ : Type*} [Finite ι] [Fintype σ]
    (x : ι → σ → L) (hx : ∀ i, x i ≠ 0) :
    ∃ c : σ → K, ∀ i, ∑ j, algebraMap K L (c j) * x i j ≠ 0 := by
  classical
  let f : ι → (σ → K) →ₗ[K] L := fun i =>
    { toFun := fun c => ∑ j, algebraMap K L (c j) * x i j
      map_add' := by
        intro a b
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
          Algebra.smul_def, mul_assoc, Finset.mul_sum] }
  have hproper : ∀ i, LinearMap.ker (f i) ≠ ⊤ := by
    intro i htop
    obtain ⟨j, hj⟩ : ∃ j, x i j ≠ 0 := by
      by_contra h
      apply hx i
      funext j
      simpa using not_exists.mp h j
    have hmem : Pi.single j (1 : K) ∈ LinearMap.ker (f i) := by
      rw [htop]
      trivial
    have hzero := LinearMap.mem_ker.mp hmem
    apply hj
    simpa [f, Pi.single_apply, eq_comm] using hzero
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun i => LinearMap.ker (f i)) hproper
  exact ⟨c, fun i => by simpa [LinearMap.mem_ker, f] using hc i⟩

/-- The common linear form is defined over K, even when all of the
projective points are represented by vectors over an arbitrary L/K. -/
theorem exists_common_groundField_linear_chart_for_nonzero_vectors
    {K : Type u} [Field K] [Infinite K]
    {L : Type v} [Field L] [Algebra K L]
    {ι : Type*} [Finite ι]
    (x : ι → Fin 4 → L) (hx : ∀ i, x i ≠ 0) :
    ∃ c : Fin 4 → K, ∀ i,
      eval₂ (algebraMap K L) (x i) (homogeneousLinearForm c) ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_groundField_dotProduct_nonzero (K := K) (L := L) x hx
  refine ⟨c, fun i => ?_⟩
  simpa [homogeneousLinearForm] using hc i

end PfaffianDescent
