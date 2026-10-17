import PfaffianDescent.HomogeneousProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PfaffianDescent
open MvPolynomial
section
variable {K σ : Type*} [Field K] [Finite σ]

/-- A polynomial automorphism preserving every homogeneous degree also has a
degree-preserving inverse. -/
theorem homogeneous_equiv_symm
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hE : ∀ d (p : MvPolynomial σ K), p.IsHomogeneous d → (E p).IsHomogeneous d)
    (d : ℕ) {p : MvPolynomial σ K} (hp : p.IsHomogeneous d) :
    (E.symm p).IsHomogeneous d := by
  let H := homogeneousSubmodule σ K d
  let F : H →ₗ[K] H := (E.toLinearMap.comp H.subtype).codRestrict H
    (fun q => hE d q.val q.property)
  have hi : Function.Injective F := by
    intro q r h
    apply Subtype.ext
    apply E.injective
    exact congrArg Subtype.val h
  have hs : Function.Surjective F := LinearMap.surjective_of_injective hi
  obtain ⟨q, hq⟩ := hs ⟨p, hp⟩
  have he : E q.val = p := congrArg Subtype.val hq
  rw [← he, AlgEquiv.symm_apply_apply]
  exact q.property

end
end PfaffianDescent
