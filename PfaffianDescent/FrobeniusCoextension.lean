import PfaffianDescent.RingFrobenius
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace PfaffianDescent
open Module CategoryTheory ModuleCat
universe u
section
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Identify the categorical restriction of the regular module with the given algebra module. -/
def restrictionRegularEquiv :
    (restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) ≃ₗ[R] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' := by
    intro r
    change ∀ x : A, algebraMap R A r * x = r • x
    intro x
    exact (Algebra.smul_def r x).symm

/-- The multiplication functional, regarded as a morphism of modules over the algebra itself. -/
noncomputable def frobeniusCoextensionMap (ell : Module.Dual R A) :
    A →ₗ[A] (coextendScalars (algebraMap R A)).obj (ModuleCat.of R R) :=
  (RestrictionCoextensionAdj.HomEquiv.fromRestriction (algebraMap R A) (Y := ModuleCat.of A A)
    (ModuleCat.ofHom (X := (restrictScalars (algebraMap R A)).obj (ModuleCat.of A A))
      (Y := ModuleCat.of R R)
      (ell.comp (restrictionRegularEquiv (R := R) (A := A)).toLinearMap))).hom

lemma frobeniusCoextensionMap_apply (ell : Module.Dual R A) (a x : A) :
    frobeniusCoextensionMap ell a x = ell (x*a) := rfl

/-- A perfect multiplication pairing is an isomorphism with coextension of scalars,
including the module action of the algebra, not just the action of the base ring. -/
theorem frobeniusCoextensionMap_bijective (ell : Module.Dual R A)
    (h : Function.Bijective (ringMultiplicationDual ell)) :
    Function.Bijective (frobeniusCoextensionMap ell) := by
  constructor
  · intro a b he
    apply h.1
    ext x
    have hx := congrArg (fun z : (coextendScalars (algebraMap R A)).obj
      (ModuleCat.of R R) => z x) he
    change ell (a*x) = ell (b*x)
    change ell (x*a) = ell (x*b) at hx
    simpa only [mul_comm] using hx
  · intro psi
    let psi' : Module.Dual R A :=
      (CoextendScalars.equiv (algebraMap R A) (ModuleCat.of R R) psi).comp
        restrictionRegularEquiv.symm.toLinearMap
    obtain ⟨a, ha⟩ := h.2 psi'
    refine ⟨a, CoextendScalars.ext ?_⟩
    apply LinearMap.ext
    change ∀ x : A, ell (x*a) = psi x
    intro x
    have hx := LinearMap.congr_fun ha x
    change ell (a*x) = psi x at hx
    simpa only [mul_comm] using hx

noncomputable def frobeniusCoextensionEquiv (ell : Module.Dual R A)
    (h : Function.Bijective (ringMultiplicationDual ell)) :
    A ≃ₗ[A] (coextendScalars (algebraMap R A)).obj (ModuleCat.of R R) :=
  LinearEquiv.ofBijective (frobeniusCoextensionMap ell) (frobeniusCoextensionMap_bijective ell h)

end
end PfaffianDescent
