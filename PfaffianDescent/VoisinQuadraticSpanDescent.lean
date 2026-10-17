import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Descending quadratic pencil membership from a field extension

The field extension used to split a finite intersection cannot introduce a
new linear relation over the ground field. In particular, if a ground-field
quadratic becomes a scalar combination of two ground-field quadrics after
extension, it was already such a combination before extension.
-/

namespace PfaffianDescent

open MvPolynomial TensorProduct

universe u

/-- Membership in a vector subspace descends from a field extension. -/
theorem mem_submodule_of_one_tmul_mem_baseChange
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V]
    (W : Submodule K V) (v : V)
    (h : (1 ⊗ₜ[K] v : L ⊗[K] V) ∈ W.baseChange L) :
    v ∈ W := by
  have hker : (1 ⊗ₜ[K] v : L ⊗[K] V) ∈
      LinearMap.ker (LinearMap.lTensor L W.mkQ) := by
    rw [lTensor_mkQ]
    exact h
  have hzero : (1 ⊗ₜ[K] W.mkQ v : L ⊗[K] (V ⧸ W)) = 0 := by
    simpa only [LinearMap.mem_ker, LinearMap.lTensor_tmul] using hker
  have hv : W.mkQ v = 0 := by
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L)
      (V ⧸ W))
    simpa using hzero
  exact (Submodule.Quotient.mk_eq_zero W).mp
    (by simpa only [Submodule.mkQ_apply] using hv)

/-- A ground-field polynomial in the extension-field span of two
ground-field polynomials already belongs to their ground-field span. -/
theorem polynomial_pair_span_descends
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (q r t : MvPolynomial (Fin 4) K)
    (h : ∃ a b : L,
      MvPolynomial.map (algebraMap K L) t =
        C a * MvPolynomial.map (algebraMap K L) q +
        C b * MvPolynomial.map (algebraMap K L) r) :
    ∃ a b : K, t = C a * q + C b * r := by
  obtain ⟨a, b, hab⟩ := h
  let W : Submodule K (MvPolynomial (Fin 4) K) := Submodule.span K ({q, r} : Set _)
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K L
  have hrel : (1 ⊗ₜ[K] t : L ⊗[K] MvPolynomial (Fin 4) K) =
      a ⊗ₜ[K] q + b ⊗ₜ[K] r := by
    apply e.injective
    simpa [e, MvPolynomial.smul_eq_C_mul] using hab
  have hq : q ∈ W := Submodule.subset_span (by simp [W])
  have hr : r ∈ W := Submodule.subset_span (by simp [W])
  have ht : (1 ⊗ₜ[K] t : L ⊗[K] MvPolynomial (Fin 4) K) ∈ W.baseChange L := by
    rw [hrel]
    exact Submodule.add_mem _
      (Submodule.tmul_mem_baseChange_of_mem a hq)
      (Submodule.tmul_mem_baseChange_of_mem b hr)
  obtain ⟨c, d, hcd⟩ := (Submodule.mem_span_pair.mp
    (mem_submodule_of_one_tmul_mem_baseChange W t ht))
  exact ⟨c, d, by simpa only [MvPolynomial.smul_eq_C_mul] using hcd.symm⟩

end PfaffianDescent
