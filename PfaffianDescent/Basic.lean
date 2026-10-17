import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Explicit algebra for `pfaffian_degree_five_to_one.tex`.
All computations use Lean's default resource limits.
-/
namespace PfaffianDescent

abbrev Vec (R : Type*) (n : ℕ) := Fin n → R
abbrev Mat (R : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) R

section Ring
variable {R : Type*} [CommRing R]

/-- Alternation includes the zero diagonal, in every characteristic. -/
def IsAlternating {n : ℕ} (A : Mat R n) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i j, A j i = -A i j

/-- The standard Pfaffian of a six by six alternating matrix, expanded
along its first row. Indices start at zero. -/
def pf6 (A : Mat R 6) : R :=
    A 0 1 * (A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)
  - A 0 2 * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)
  + A 0 3 * (A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)
  - A 0 4 * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)
  + A 0 5 * (A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)

/-- The alternating matrix associated with its strict upper triangle. -/
def skew6 (A : Mat R 6) : Mat R 6 :=
  !![0, A 0 1, A 0 2, A 0 3, A 0 4, A 0 5;
    -A 0 1, 0, A 1 2, A 1 3, A 1 4, A 1 5;
    -A 0 2, -A 1 2, 0, A 2 3, A 2 4, A 2 5;
    -A 0 3, -A 1 3, -A 2 3, 0, A 3 4, A 3 5;
    -A 0 4, -A 1 4, -A 2 4, -A 3 4, 0, A 4 5;
    -A 0 5, -A 1 5, -A 2 5, -A 3 5, -A 4 5, 0]

theorem skew6_eq (A : Mat R 6) (hA : IsAlternating A) : skew6 A = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (hA.1 _).symm | exact (hA.2 _ _).symm

theorem pf6_smul (c : R) (A : Mat R 6) : pf6 (c • A) = c ^ 3 * pf6 A := by
  simp only [pf6, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Evaluation of the matrix pencil on homogeneous coordinates. -/
def pencil (A : Fin 4 → Mat R 6) (x : Vec R 4) : Mat R 6 :=
  x 0 • A 0 + x 1 • A 1 + x 2 • A 2 + x 3 • A 3

theorem pencil_smul (A : Fin 4 → Mat R 6) (c : R) (x : Vec R 4) :
    pencil A (c • x) = c • pencil A x := by
  ext i j
  simp [pencil, mul_add, mul_assoc]

theorem pf6_pencil_homogeneous (A : Fin 4 → Mat R 6) (c : R) (x : Vec R 4) :
    pf6 (pencil A (c • x)) = c ^ 3 * pf6 (pencil A x) := by
  rw [pencil_smul, pf6_smul]

/-- A rational projective point is represented by nonzero homogeneous coordinates. -/
def HasPfaffianPoint (A : Fin 4 → Mat R 6) : Prop :=
  ∃ x : Vec R 4, x ≠ 0 ∧ pf6 (pencil A x) = 0

/-- The deformation used in Theorem 3.2, retaining the fourth matrix. -/
def deform (A : Fin 4 → Mat R 6) (B : Fin 3 → Mat R 6) (t : R) :
    Fin 4 → Mat R 6 :=
  ![(1 - t) • A 0 + t • B 0, (1 - t) • A 1 + t • B 1,
    (1 - t) • A 2 + t • B 2, A 3]

@[simp] theorem deform_zero (A : Fin 4 → Mat R 6) (B : Fin 3 → Mat R 6) :
    deform A B 0 = A := by
  funext i
  fin_cases i
  · change (1 - (0 : R)) • A 0 + (0 : R) • B 0 = A 0
    rw [sub_zero, one_smul, zero_smul, add_zero]
  · change (1 - (0 : R)) • A 1 + (0 : R) • B 1 = A 1
    rw [sub_zero, one_smul, zero_smul, add_zero]
  · change (1 - (0 : R)) • A 2 + (0 : R) • B 2 = A 2
    rw [sub_zero, one_smul, zero_smul, add_zero]
  · rfl

@[simp] theorem deform_one (A : Fin 4 → Mat R 6) (B : Fin 3 → Mat R 6) :
    deform A B 1 = ![B 0, B 1, B 2, A 3] := by
  funext i
  fin_cases i
  · change (1 - (1 : R)) • A 0 + (1 : R) • B 0 = B 0
    rw [sub_self, zero_smul, one_smul, zero_add]
  · change (1 - (1 : R)) • A 1 + (1 : R) • B 1 = B 1
    rw [sub_self, zero_smul, one_smul, zero_add]
  · change (1 - (1 : R)) • A 2 + (1 : R) • B 2 = B 2
    rw [sub_self, zero_smul, one_smul, zero_add]
  · rfl

end Ring
end PfaffianDescent
