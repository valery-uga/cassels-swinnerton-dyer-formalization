import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A local chart for a varying quadratic evaluation kernel

When eight chosen quadratic evaluations form an invertible block, the full
ten-to-eight evaluation kernel is the graph of a map from the remaining two
coefficients.  This elementary statement works over a commutative ring, so
it can be applied on an open of the actual configuration scheme rather than
only over a field-valued fiber.
-/

namespace PfaffianDescent

open Module

universe u v w

variable {R : Type u} [CommRing R]
  {U : Type v} [AddCommGroup U] [Module R U]
  {V : Type w} [AddCommGroup V] [Module R V]
  {W : Type*} [AddCommGroup W] [Module R W]

/-- An evaluation map written in an invertible eight-column block and a
two-column complementary block. -/
def quadraticBlockEvaluation (A : U ≃ₗ[R] W) (B : V →ₗ[R] W) :
    U × V →ₗ[R] W :=
  A.toLinearMap.comp (LinearMap.fst R U V) +
    B.comp (LinearMap.snd R U V)

@[simp] theorem quadraticBlockEvaluation_apply
    (A : U ≃ₗ[R] W) (B : V →ₗ[R] W) (u : U) (v : V) :
    quadraticBlockEvaluation A B (u, v) = A u + B v := rfl

/-- The projection of the evaluation kernel to the two complementary
coefficients is a linear equivalence. -/
noncomputable def quadraticBlockKernelEquiv
    (A : U ≃ₗ[R] W) (B : V →ₗ[R] W) :
    LinearMap.ker (quadraticBlockEvaluation A B) ≃ₗ[R] V := by
  let g : LinearMap.ker (quadraticBlockEvaluation A B) →ₗ[R] V :=
    (LinearMap.snd R U V).comp
      (LinearMap.ker (quadraticBlockEvaluation A B)).subtype
  have hsurj : Function.Surjective g := by
    intro v
    let u := -A.symm (B v)
    have hzero : quadraticBlockEvaluation A B (u, v) = 0 := by
      simp [u, quadraticBlockEvaluation_apply]
    exact ⟨⟨(u, v), hzero⟩, rfl⟩
  have hinj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · have hx := x.property
      have hy := y.property
      have hfirst : A x.1.1 = A y.1.1 := by
        have hsecond : x.1.2 = y.1.2 := hxy
        change A x.1.1 + B x.1.2 = 0 at hx
        change A y.1.1 + B y.1.2 = 0 at hy
        rw [hsecond] at hx
        exact add_right_cancel (hx.trans hy.symm)
      exact A.injective hfirst
    · exact hxy
  exact LinearEquiv.ofBijective g ⟨hinj, hsurj⟩

/-- The kernel vector with prescribed complementary coefficients has an
explicit first block. -/
theorem quadraticBlockKernelEquiv_symm_apply
    (A : U ≃ₗ[R] W) (B : V →ₗ[R] W) (v : V) :
    (quadraticBlockKernelEquiv A B).symm v =
      ⟨(-A.symm (B v), v), by
        simp [quadraticBlockEvaluation_apply]⟩ := by
  apply (quadraticBlockKernelEquiv A B).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- On a full-rank eight-column chart, the two free coefficients give an
actual basis of the varying quadratic kernel over the chart ring. -/
noncomputable def quadraticBlockKernelBasis
    (A : (Fin 8 → R) ≃ₗ[R] (Fin 8 → R))
    (B : (Fin 2 → R) →ₗ[R] (Fin 8 → R)) :
    Basis (Fin 2) R
      (LinearMap.ker (quadraticBlockEvaluation A B)) :=
  (Pi.basisFun R (Fin 2)).map (quadraticBlockKernelEquiv A B).symm

/-- The local quadratic kernel has constant rank two wherever its chosen
eight-column evaluation block is invertible. -/
theorem quadraticBlockKernel_finrank_two
    [Nontrivial R] [StrongRankCondition R]
    (A : (Fin 8 → R) ≃ₗ[R] (Fin 8 → R))
    (B : (Fin 2 → R) →ₗ[R] (Fin 8 → R)) :
    Module.finrank R (LinearMap.ker (quadraticBlockEvaluation A B)) = 2 := by
  rw [(quadraticBlockKernelEquiv A B).finrank_eq]
  rw [Module.finrank_pi]
  simp

/-- A unit eight-by-eight evaluation minor supplies the local frame without
choosing an inverse matrix by hand.  The hypothesis is meaningful over a
coordinate ring or its localization as well as over a field. -/
noncomputable def quadraticMatrixBlockKernelBasis
    (A : Matrix (Fin 8) (Fin 8) R) (hA : IsUnit A.det)
    (B : Matrix (Fin 8) (Fin 2) R) :
    Basis (Fin 2) R
      (LinearMap.ker
        (quadraticBlockEvaluation
          (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8)) A hA) (Matrix.toLin' B))) :=
  quadraticBlockKernelBasis
    (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8)) A hA) (Matrix.toLin' B)

/-- The same minor gives constant rank two for the entire evaluation
kernel on this chart. -/
theorem quadraticMatrixBlockKernel_finrank_two
    [Nontrivial R] [StrongRankCondition R]
    (A : Matrix (Fin 8) (Fin 8) R) (hA : IsUnit A.det)
    (B : Matrix (Fin 8) (Fin 2) R) :
    Module.finrank R
      (LinearMap.ker
        (quadraticBlockEvaluation
          (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8)) A hA) (Matrix.toLin' B))) = 2 :=
  quadraticBlockKernel_finrank_two
    (Matrix.toLinearEquiv (Pi.basisFun R (Fin 8)) A hA) (Matrix.toLin' B)

/-- A full-rank specialization certifies that the same evaluation minor is
not the zero function on the parameter ring. -/
theorem quadraticMatrixBlock_det_ne_zero_of_specialization_unit
    {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S) (A : Matrix (Fin 8) (Fin 8) R)
    (hA : IsUnit (A.map f).det) : A.det ≠ 0 := by
  intro hzero
  have hmap : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  rw [hzero, map_zero] at hmap
  exact hA.ne_zero hmap

/-- A minor invertible at one specialized fiber is invertible over the
fraction field of an integral parameter ring. -/
theorem quadraticMatrixBlock_generic_det_unit_of_specialization_unit
    [IsDomain R]
    {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S) (A : Matrix (Fin 8) (Fin 8) R)
    (hA : IsUnit (A.map f).det) :
    IsUnit (A.map (algebraMap R (FractionRing R))).det := by
  have hdet : A.det ≠ 0 :=
    quadraticMatrixBlock_det_ne_zero_of_specialization_unit f A hA
  have hmap : (A.map (algebraMap R (FractionRing R))).det =
      algebraMap R (FractionRing R) A.det :=
    (RingHom.map_det (algebraMap R (FractionRing R)) A).symm
  rw [hmap]
  exact isUnit_iff_ne_zero.mpr
    (IsFractionRing.to_map_eq_zero_iff.not.mpr hdet)

/-- The local quadratic kernel basis therefore exists on the generic fiber
whenever one field-valued specialization has a full-rank minor. -/
noncomputable def quadraticMatrixBlockGenericKernelBasis
    [IsDomain R]
    {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S)
    (A : Matrix (Fin 8) (Fin 8) R)
    (B : Matrix (Fin 8) (Fin 2) R)
    (hA : IsUnit (A.map f).det) :
    Basis (Fin 2) (FractionRing R)
      (LinearMap.ker
        (quadraticBlockEvaluation
          (Matrix.toLinearEquiv
            (Pi.basisFun (FractionRing R) (Fin 8))
            (A.map (algebraMap R (FractionRing R)))
            (quadraticMatrixBlock_generic_det_unit_of_specialization_unit f A hA))
          (Matrix.toLin' (B.map (algebraMap R (FractionRing R)))))) :=
  quadraticMatrixBlockKernelBasis
    (A.map (algebraMap R (FractionRing R)))
    (quadraticMatrixBlock_generic_det_unit_of_specialization_unit f A hA)
    (B.map (algebraMap R (FractionRing R)))

end PfaffianDescent
