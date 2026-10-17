import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import PfaffianDescent.QuarticTangentConstruction

/-!
# Trace duality in the tangent-direction construction

This is the linear algebra in the final paragraph of Proposition 5.5 of
`2-proofs.tex`.  For a separable degree-four residue field, it identifies a
`k`-linear functional on a two-dimensional `L`-space with trace after an
`L`-linear functional.
-/

namespace PfaffianDescent
namespace QuarticNet

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The trace pairing identifies a separable field extension with its
`K`-linear dual. -/
noncomputable def traceDualEquiv : L ≃ₗ[K] Module.Dual K L :=
  (Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)

theorem traceDualEquiv_apply (a x : L) :
    traceDualEquiv (K := K) (L := L) a x = Algebra.trace K L (a * x) := by
  rw [traceDualEquiv, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]

/-- Inserting one coordinate of `L²`, as a `K`-linear map. -/
def traceDualCoordinateInjection (i : Fin 2) : L →ₗ[K] (Fin 2 → L) where
  toFun z := Pi.single i z
  map_add' x y := by
    ext j
    by_cases h : j = i <;> simp [h]
  map_smul' a x := by
    ext j
    by_cases h : j = i <;> simp [h]

/-- The `L`-linear functional whose trace is a prescribed `K`-linear
functional on `L²`. -/
noncomputable def traceDualFactor (ell : Module.Dual K (Fin 2 → L)) :
    (Fin 2 → L) →ₗ[L] L where
  toFun z := ∑ i, z i * (traceDualEquiv (K := K) (L := L)).symm
    (ell.comp (traceDualCoordinateInjection (K := K) (L := L) i))
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply]
    ring

/-- Trace after `traceDualFactor` recovers the original `K`-linear
functional. This is the trace-duality isomorphism used in Proposition 5.5,
written in a chosen two-coordinate basis. -/
theorem trace_comp_traceDualFactor (ell : Module.Dual K (Fin 2 → L))
    (z : Fin 2 → L) :
    Algebra.trace K L (traceDualFactor (K := K) (L := L) ell z) = ell z := by
  let c : Fin 2 → L := fun i => (traceDualEquiv (K := K) (L := L)).symm
    (ell.comp (traceDualCoordinateInjection (K := K) (L := L) i))
  have hz : z = ∑ i, traceDualCoordinateInjection (K := K) (L := L) i (z i) := by
    ext j
    symm
    change (∑ i, Pi.single i (z i)) j = z j
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg hij.symm]
    · simp
  have htrace : Algebra.trace K L (traceDualFactor (K := K) (L := L) ell z) =
      ∑ i, ell (traceDualCoordinateInjection (K := K) (L := L) i (z i)) := by
    change Algebra.trace K L (∑ i, z i * c i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show z i * c i = c i * z i by ring, ← traceDualEquiv_apply]
    simp [c]
  calc
    Algebra.trace K L (traceDualFactor (K := K) (L := L) ell z) =
        ∑ i, ell (traceDualCoordinateInjection (K := K) (L := L) i (z i)) := htrace
    _ = ell (∑ i, traceDualCoordinateInjection (K := K) (L := L) i (z i)) :=
      (map_sum ell (fun i => traceDualCoordinateInjection (K := K) (L := L) i (z i))
        Finset.univ).symm
    _ = ell z := congrArg ell hz.symm

/-- The full linear-algebra conclusion of Proposition 5.5: for a degree-four
separable residue field, a map from six `K`-parameters to a two-dimensional
`L`-space has a nonzero `L`-linear quotient whose trace kills the map. -/
theorem exists_trace_quotient_annihilating_six_to_two
    (hdim : Module.finrank K L = 4)
    (φ : (Fin 6 → K) →ₗ[K] (Fin 2 → L)) :
    ∃ q : (Fin 2 → L) →ₗ[L] L, q ≠ 0 ∧
      ∀ v : Fin 6 → K, Algebra.trace K L (q (φ v)) = 0 := by
  have htarget : Module.finrank K (Fin 2 → L) = 8 := by
    rw [Module.finrank_pi_fintype]
    simp [hdim]
  obtain ⟨ell, hell, hellφ⟩ := exists_nonzero_dual_annihilating_of_finrank_lt φ (by
    rw [show Module.finrank K (Fin 6 → K) = 6 by simp, htarget]
    norm_num)
  refine ⟨traceDualFactor (K := K) (L := L) ell, ?_, ?_⟩
  · intro hzero
    apply hell
    apply LinearMap.ext
    intro z
    rw [← trace_comp_traceDualFactor ell z, hzero]
    simp
  · intro v
    rw [trace_comp_traceDualFactor]
    exact hellφ v

/-- A nonzero linear map to a one-dimensional vector space over a field is
surjective, so the functional constructed above really is a quotient. -/
theorem linearMap_surjective_to_field_of_ne_zero
    {E : Type*} [AddCommGroup E] [Module L E]
    (q : E →ₗ[L] L) (hq : q ≠ 0) : Function.Surjective q := by
  have hx : ∃ x : E, q x ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    apply LinearMap.ext
    intro x
    exact h x
  obtain ⟨x, hx⟩ := hx
  intro y
  refine ⟨(y * (q x)⁻¹) • x, ?_⟩
  rw [map_smul]
  change (y * (q x)⁻¹) * q x = y
  field_simp [hx]

/-- The quotient in the tangent construction can be chosen surjective. -/
theorem exists_surjective_trace_quotient_annihilating_six_to_two
    (hdim : Module.finrank K L = 4)
    (φ : (Fin 6 → K) →ₗ[K] (Fin 2 → L)) :
    ∃ q : (Fin 2 → L) →ₗ[L] L, Function.Surjective q ∧
      ∀ v : Fin 6 → K, Algebra.trace K L (q (φ v)) = 0 := by
  obtain ⟨q, hq, hqφ⟩ := exists_trace_quotient_annihilating_six_to_two hdim φ
  exact ⟨q, linearMap_surjective_to_field_of_ne_zero q hq, hqφ⟩

end
end QuarticNet
end PfaffianDescent
