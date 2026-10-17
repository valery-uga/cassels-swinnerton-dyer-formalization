import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open Module

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The multiplication pairing associated to a linear functional on a finite algebra. -/
def algebraMultiplicationDual (ell : Module.Dual K A) : A →ₗ[K] Module.Dual K A where
  toFun v :=
    { toFun := fun w => ell (v * w)
      map_add' := by intro x y; rw [mul_add, map_add]
      map_smul' := by intro c x; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro v w
    ext x
    change ell ((v+w)*x) = ell (v*x) + ell (w*x)
    rw [add_mul, map_add]
  map_smul' := by
    intro c v
    ext x
    change ell ((c • v)*x) = c • ell (v*x)
    rw [smul_mul_assoc, map_smul]

/-- A Frobenius functional has a nondegenerate multiplication pairing. -/
def IsFrobeniusFunctional (ell : Module.Dual K A) : Prop :=
  Function.Injective (algebraMultiplicationDual ell)

variable [FiniteDimensional K A]

theorem frobeniusFunctional_surjective (ell : Module.Dual K A) (h : IsFrobeniusFunctional ell) :
    Function.Surjective (algebraMultiplicationDual ell) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show finrank K A = finrank K (Module.Dual K A) by rw [Subspace.dual_finrank_eq])).mp
  exact h

/-- Two nondegenerate multiplication functionals differ by multiplication by a unit.
This is the algebra version of the hyperplane normalization used for field points. -/
theorem frobenius_functionals_multiplicative (ell psi : Module.Dual K A)
    (hell : IsFrobeniusFunctional ell) (hpsi : IsFrobeniusFunctional psi) :
    ∃ u : Aˣ, ∀ a : A, ell (u.val * a) = psi a := by
  obtain ⟨v, hv⟩ := frobeniusFunctional_surjective ell hell psi
  have hev (a : A) : ell (v*a) = psi a := LinearMap.congr_fun hv a
  have hinj : Function.Injective (LinearMap.mulLeft K v) := by
    intro a b hab
    apply hpsi
    ext w
    change psi (a*w) = psi (b*w)
    rw [← hev, ← hev, ← mul_assoc, ← mul_assoc]
    exact congrArg (fun z : A => ell (z*w)) hab
  have hsurj : Function.Surjective (LinearMap.mulLeft K v) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  obtain ⟨w, hw⟩ := hsurj 1
  have hvw : v*w = 1 := hw
  refine ⟨⟨v,w,hvw,(mul_comm w v).trans hvw⟩, ?_⟩
  exact hev

end
end PfaffianDescent
