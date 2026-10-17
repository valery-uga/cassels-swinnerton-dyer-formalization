import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import PfaffianDescent.VoisinGradedMultiplicationFiberCriterion

/-!
# Regularity from degreewise injectivity

Multiplication by a homogeneous equation is injective on a graded ring
if it is injective on each homogeneous component. This connects the
degreewise flatness criterion to regularity of an entire coordinate ring.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

/-- An element homogeneous of degree `d` is regular if multiplication
by it is injective from every degree `n` into degree `n+d`. -/
theorem isRegular_of_homogeneousPiece_mul_injective
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d : ℕ} (s : 𝒜 d)
    (h : ∀ n : ℕ, Function.Injective
      (fun x : 𝒜 n =>
        (⟨(x : A) * (s : A), SetLike.mul_mem_graded x.2 s.2⟩ : 𝒜 (n + d)))) :
    IsRegular (s : A) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  have hx' : x * (s : A) = 0 := by simpa only [mul_comm] using hx
  have hxgrade (n : ℕ) : DirectSum.decompose 𝒜 x n = 0 := by
    apply h n
    apply Subtype.ext
    have hmul := DirectSum.coe_decompose_mul_add_of_right_mem
      (𝒜 := 𝒜) (i := n) (j := d) s.2 (a := x)
    rw [hx', DirectSum.decompose_zero] at hmul
    simpa using hmul.symm
  apply (DirectSum.decomposeLinearEquiv 𝒜).injective
  apply DFinsupp.ext
  intro n
  simpa only [map_zero, DirectSum.decomposeLinearEquiv_apply, DFinsupp.zero_apply]
    using hxgrade n

/-- For the actual homogeneous coordinate quotient, injectivity of all
degreewise multiplication maps implies regularity of the equation in the
whole coordinate ring. -/
theorem coordinateRing_isRegular_of_homogeneousMultiplication_injective
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    {d : ℕ} (s : grading J d)
    (h : ∀ n : ℕ, Function.Injective (homogeneousMultiplication J s n)) :
    IsRegular (s : CoordinateRing J) := by
  letI := gradedRing J
  exact isRegular_of_homogeneousPiece_mul_injective (grading J) s h

end PfaffianDescent
