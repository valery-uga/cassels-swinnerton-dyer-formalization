import PfaffianDescent.TraceFrobenius
import PfaffianDescent.ReducedFiniteAlgebraEtale
import Mathlib.RingTheory.Etale.Field

/-!
# Reduced finite algebras are Frobenius in characteristic zero

A finite reduced algebra over a characteristic-zero field is a product of
finite separable field extensions.  The sum of the field traces on that
product is a nondegenerate multiplication functional.  Transporting it
through the product decomposition supplies the Frobenius functional used in
the residual constructions in Voisin's argument.
-/

namespace PfaffianDescent

open Module
open scoped BigOperators

section Transport

variable {K A B : Type*} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Pull a linear functional back through an algebra equivalence. -/
noncomputable def frobeniusFunctionalPullback
    (e : A ≃ₐ[K] B) (ell : Module.Dual K B) : Module.Dual K A :=
  ell.comp e.toLinearMap

/-- Nondegeneracy of the multiplication functional is invariant under an
algebra equivalence. -/
theorem frobeniusFunctionalPullback_isFrobenius
    (e : A ≃ₐ[K] B) (ell : Module.Dual K B)
    (hell : IsFrobeniusFunctional ell) :
    IsFrobeniusFunctional (frobeniusFunctionalPullback e ell) := by
  intro a b hab
  apply e.injective
  apply hell
  ext y
  change ell (e a * y) = ell (e b * y)
  have hy := LinearMap.congr_fun hab (e.symm y)
  change ell (e (a * e.symm y)) = ell (e (b * e.symm y)) at hy
  simpa only [map_mul, e.apply_symm_apply] using hy

end Transport

section Product

variable {K : Type*} [Field K]
variable {I : Type*} [Finite I]
variable (L : I → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  [∀ i, FiniteDimensional K (L i)] [∀ i, Algebra.IsSeparable K (L i)]

/-- The sum of the field traces on a finite product of separable field
extensions. -/
noncomputable def productFieldTraceFunctional :
    Module.Dual K (∀ i, L i) := by
  letI := Fintype.ofFinite I
  exact
    { toFun := fun a ↦ ∑ i, Algebra.trace K (L i) (a i)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }

/-- The product trace has nondegenerate multiplication pairing. -/
theorem productFieldTraceFunctional_isFrobenius :
    IsFrobeniusFunctional (productFieldTraceFunctional (K := K) L) := by
  classical
  letI := Fintype.ofFinite I
  intro a b hab
  funext i
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate K (L i)).1 (a i - b i)
  intro x
  have hx := LinearMap.congr_fun hab (Pi.single i x)
  change (∑ j, Algebra.trace K (L j) (a j * Pi.single i x j)) =
    ∑ j, Algebra.trace K (L j) (b j * Pi.single i x j) at hx
  have hleft : (∑ j, Algebra.trace K (L j) (a j * Pi.single i x j)) =
      Algebra.trace K (L i) (a i * x) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      simp
    · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  have hright : (∑ j, Algebra.trace K (L j) (b j * Pi.single i x j)) =
      Algebra.trace K (L i) (b i * x) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      simp
    · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  rw [hleft, hright] at hx
  rw [Algebra.traceForm_apply, sub_mul, map_sub, hx, sub_self]

end Product

section Reduced

variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
  [Module.Finite K A] [IsReduced A]

/-- Every finite reduced algebra over a characteristic-zero field admits an
actual Frobenius functional. -/
theorem reducedFiniteAlgebra_exists_frobeniusFunctional :
    ∃ ell : Module.Dual K A, IsFrobeniusFunctional ell := by
  have hetale : Algebra.Etale K A := reduced_finite_algebra_etale
  obtain ⟨I, hI, L, hField, hAlgebra, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp hetale
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlgebra i
  letI (i : I) : Module.Finite K (L i) := (hfinite i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hfinite i).2
  let ell := productFieldTraceFunctional (K := K) L
  exact ⟨frobeniusFunctionalPullback e ell,
    frobeniusFunctionalPullback_isFrobenius e ell
      (productFieldTraceFunctional_isFrobenius (K := K) L)⟩

end Reduced

end PfaffianDescent
