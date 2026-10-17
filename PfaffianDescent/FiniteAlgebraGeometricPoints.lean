import PfaffianDescent.ReducedFiniteAlgebraEtale
import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace PfaffianDescent
open Module
open scoped TensorProduct
section
variable {K A L : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [IsReduced A] [Field L] [IsSepClosed L] [Algebra K L]

/-- A reduced finite algebra has as many distinct geometric evaluations as
its vector-space dimension. No enumeration or splitting hypothesis is assumed. -/
theorem reduced_finite_algebra_distinct_geometric_evaluations (n : ℕ) (hdim : finrank K A = n) :
    ∃ ev : Fin n → A →ₐ[K] L, Function.Injective ev := by
  classical
  have : Algebra.Etale K A := reduced_finite_algebra_etale
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun L (L ⊗[K] A)
  have hm : m = n := by
    have h := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype, finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, hdim] at h
    exact h.symm
  subst m
  let v : Fin n → (L ⊗[K] A) →ₐ[L] L := fun i => (Pi.evalAlgHom L (fun _ : Fin n => L) i).comp e.toAlgHom
  have hv : Function.Injective v := by
    intro i j hij
    by_contra hne
    have hh := DFunLike.congr_fun hij (e.symm (Pi.single i 1))
    change e (e.symm (Pi.single i 1)) i = e (e.symm (Pi.single i 1)) j at hh
    simp only [e.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at hh
    exact one_ne_zero hh
  let E := Algebra.TensorProduct.liftEquivRight K L A L
  exact ⟨E.symm ∘ v, E.symm.injective.comp hv⟩

end
end PfaffianDescent
