import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! Native graded-ideal projection of an existing linear-factor witness.
The actual original caller derives this witness from its exact restriction
kernel. No graded-piece/global-section comparison is introduced. -/
noncomputable section
namespace PfaffianDescent.Coray
universe u v

/-- Project a genuine ideal witness to the necessary complementary degree.
The ideal's homogeneity keeps the projected element in that SAME ideal. -/
theorem homogeneousIdeal_linearFactor_exists_complementaryDegree
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [GradedRing G]
    (J : Ideal A) (hJ : J.IsHomogeneous G)
    (H : A) (hH : H ∈ G 1) (d : ℕ) (hd : 1 ≤ d)
    (y : A) (hy : y ∈ G d) (z : A) (hz : z ∈ J) (hzy : H * z = y) :
    ∃ w : A, w ∈ J ∧ w ∈ G (d - 1) ∧ H * w = y := by
  refine ⟨(DirectSum.decompose G z (d - 1) : A), hJ (d - 1) hz,
    (DirectSum.decompose G z (d - 1)).property, ?_⟩
  have hproj := DirectSum.coe_decompose_mul_of_left_mem_of_le
    G (b := z) hH hd
  rw [hzy, DirectSum.decompose_of_mem_same G hy] at hproj
  exact hproj.symm

/-- A degree-zero element in the image of multiplication by a linear form
is zero. No domain, cancellation or ideal saturation hypothesis is needed. -/
theorem homogeneous_linearFactor_degreeZero_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [GradedRing G]
    (H : A) (hH : H ∈ G 1) (y : A) (hy : y ∈ G 0)
    (z : A) (hzy : H * z = y) : y = 0 := by
  have hproj := DirectSum.coe_decompose_mul_of_left_mem_of_not_le
    G (b := z) hH (by decide : ¬ (1 : ℕ) ≤ 0)
  rw [hzy, DirectSum.decompose_of_mem_same G hy] at hproj
  exact hproj

end PfaffianDescent.Coray
