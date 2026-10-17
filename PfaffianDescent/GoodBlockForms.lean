import PfaffianDescent.GoodSpectralProjectors
import PfaffianDescent.GoodTriple
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace PfaffianDescent
open Module
open LinearMap (BilinForm)
section
variable (R : Type*) [CommRing R]

/-- The standard alternating form on one of the two-dimensional blocks. -/
def goodPlaneForm : BilinForm R (Fin 2 → R) := Matrix.toBilin' !![0, 1; -1, 0]

lemma goodPlaneForm_apply (x y : Fin 2 → R) :
    goodPlaneForm R x y = x 0 * y 1 - x 1 * y 0 := by
  simp [goodPlaneForm, Matrix.toBilin'_apply, Fin.sum_univ_two, sub_eq_add_neg]

/-- The direct sum of the three standard symplectic forms. -/
def goodSymplecticForm : BilinForm R (Fin 3 → Fin 2 → R) :=
  ∑ i : Fin 3, (goodPlaneForm R).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

lemma goodSymplecticForm_apply (x y : Fin 3 → Fin 2 → R) :
    goodSymplecticForm R x y = ∑ i : Fin 3, (x i 0 * y i 1 - x i 1 * y i 0) := by
  simp [goodSymplecticForm, goodPlaneForm_apply]

lemma goodSymplecticForm_single_right (x : Fin 3 → Fin 2 → R) (i : Fin 3)
    (y : Fin 2 → R) :
    goodSymplecticForm R x (Pi.single i y) = goodPlaneForm R (x i) y := by
  classical
  fin_cases i <;> simp [goodSymplecticForm_apply, Pi.single_apply,
    goodPlaneForm_apply, Fin.sum_univ_three]

lemma goodSymplecticForm_single_left (i : Fin 3) (x : Fin 2 → R)
    (y : Fin 3 → Fin 2 → R) :
    goodSymplecticForm R (Pi.single i x) y = goodPlaneForm R x (y i) := by
  classical
  fin_cases i <;> simp [goodSymplecticForm_apply, Pi.single_apply,
    goodPlaneForm_apply, Fin.sum_univ_three]

lemma goodSymplecticForm_isAlt : (goodSymplecticForm R).IsAlt := by
  intro x
  simp [goodSymplecticForm_apply, mul_comm]

lemma goodSymplecticForm_nondegenerate : (goodSymplecticForm R).Nondegenerate := by
  constructor
  · intro x hx
    ext i j
    have h0 := hx (Pi.single i ![0, 1])
    have h1 := hx (Pi.single i ![1, 0])
    rw [goodSymplecticForm_single_right, goodPlaneForm_apply] at h0 h1
    fin_cases j
    · simpa using h0
    · simpa using h1
  · intro y hy
    ext i j
    have h0 := hy (Pi.single i ![0, 1])
    have h1 := hy (Pi.single i ![1, 0])
    rw [goodSymplecticForm_single_left, goodPlaneForm_apply] at h0 h1
    fin_cases j
    · simpa using h0
    · simpa using h1

/-- Interleaved six coordinates are precisely three two-dimensional blocks. -/
def goodBlockCoordinates : (Fin 6 → R) ≃ₗ[R] (Fin 3 → Fin 2 → R) where
  toFun x := ![![x 0, x 1], ![x 2, x 3], ![x 4, x 5]]
  invFun x := ![x 0 0, x 0 1, x 1 0, x 1 1, x 2 0, x 2 1]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma goodTriple_zero_block_form (x y : Fin 6 → R) :
    (goodTriple 0 : Mat R 6).toBilin' x y =
      goodSymplecticForm R (goodBlockCoordinates R x) (goodBlockCoordinates R y) := by
  simp [Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodSymplecticForm_apply, Fin.sum_univ_three, goodBlockCoordinates]
  ring

lemma goodTriple_one_block_form (x y : Fin 6 → R) :
    (goodTriple 1 : Mat R 6).toBilin' x y =
      goodSymplecticForm R (goodBlockCoordinates R x)
        (goodSpectralOperator R (Fin 2 → R) (goodBlockCoordinates R y)) := by
  simp [Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodSymplecticForm_apply, Fin.sum_univ_three, goodBlockCoordinates, goodSpectralOperator]
  ring

end
section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An isotropic subspace of half the ambient dimension is its own orthogonal. -/
lemma isotropic_eq_orthogonal_of_half (B : BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hdim : 2 * finrank K W = finrank K V)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) : W = B.orthogonal W := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro y hy
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr (fun x hx => hiso x hx y hy)
  · rw [LinearMap.BilinForm.finrank_orthogonal hB]
    omega

/-- Two isotropy conditions imply invariance under their relative operator. -/
lemma invariant_of_two_isotropic (B C : BilinForm K V) (hB : B.Nondegenerate)
    (T : V →ₗ[K] V) (hT : ∀ x y, C x y = B x (T y))
    (W : Submodule K V) (hdim : 2 * finrank K W = finrank K V)
    (hisoB : ∀ x ∈ W, ∀ y ∈ W, B x y = 0)
    (hisoC : ∀ x ∈ W, ∀ y ∈ W, C x y = 0) : ∀ y ∈ W, T y ∈ W := by
  intro y hy
  rw [isotropic_eq_orthogonal_of_half B hB W hdim hisoB]
  apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
  intro x hx
  rw [← hT]
  exact hisoC x hx y hy

end
end PfaffianDescent
