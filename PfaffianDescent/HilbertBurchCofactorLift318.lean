import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Maps

/-!
Algebraic support for lifting a codimension-two determinantal presentation.
This file constructs the cofactor relation and its compatibility with reduction.
It does not assert existence or exactness of a Hilbert–Burch presentation, or
flatness of the lifted quotient; those are separate mathematical obligations.
-/

noncomputable section
namespace PfaffianDescent
open Matrix

variable {R S : Type*} [CommRing R] [CommRing S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Add a zero column to a matrix with one more row than columns. -/
def hilbertBurchAugment318 (M : Matrix (Option ι) ι R) :
    Matrix (Option ι) (Option ι) R :=
  fun i j => Option.elim j 0 (M i)

/-- The cofactor row of the added zero column. Its entries are the signed
maximal minors, with signs encoded by the adjugate convention. -/
def hilbertBurchCofactors318 (M : Matrix (Option ι) ι R) : Option ι → R :=
  (hilbertBurchAugment318 M).adjugate none

lemma hilbertBurchAugment_det318 (M : Matrix (Option ι) ι R) :
    (hilbertBurchAugment318 M).det = 0 :=
  Matrix.det_eq_zero_of_column_eq_zero none (fun _ => rfl)

/-- The determinantal generators satisfy the prescribed matrix relations
over every commutative ring, including across nilpotent extensions. -/
theorem hilbertBurchCofactors_relation318 (M : Matrix (Option ι) ι R) (j : ι) :
    ∑ i, hilbertBurchCofactors318 M i * M i j = 0 := by
  have h := congrArg (fun A : Matrix (Option ι) (Option ι) R => A none (some j))
    (Matrix.adjugate_mul (hilbertBurchAugment318 M))
  simpa [Matrix.mul_apply, hilbertBurchCofactors318, hilbertBurchAugment318,
    hilbertBurchAugment_det318] using h

lemma hilbertBurchAugment_map318 (f : R →+* S) (M : Matrix (Option ι) ι R) :
    f.mapMatrix (hilbertBurchAugment318 M) = hilbertBurchAugment318 (M.map f) := by
  ext i j
  cases j <;> simp [hilbertBurchAugment318]

theorem hilbertBurchCofactors_map318 (f : R →+* S) (M : Matrix (Option ι) ι R)
    (i : Option ι) :
    f (hilbertBurchCofactors318 M i) = hilbertBurchCofactors318 (M.map f) i := by
  have h := congrArg (fun A : Matrix (Option ι) (Option ι) S => A none i)
    (f.map_adjugate (hilbertBurchAugment318 M))
  rw [hilbertBurchAugment_map318] at h
  exact h

/-- An arbitrary matrix lifts through a surjective ring map. Its determinantal
generators reduce to the original generators, and the lifted syzygies hold
exactly upstairs. No flatness conclusion is hidden in this elementary step. -/
theorem exists_hilbertBurch_matrix_lift318 (f : R →+* S) (hf : Function.Surjective f)
    (M : Matrix (Option ι) ι S) :
    ∃ N : Matrix (Option ι) ι R,
      N.map f = M ∧
      (∀ i, f (hilbertBurchCofactors318 N i) = hilbertBurchCofactors318 M i) ∧
      (∀ j, ∑ i, hilbertBurchCofactors318 N i * N i j = 0) := by
  choose entries hN using fun i j => hf (M i j)
  let N : Matrix (Option ι) ι R := Matrix.of entries
  have hmap : N.map f = M := by ext i j; exact hN i j
  refine ⟨N, hmap, ?_, hilbertBurchCofactors_relation318 N⟩
  intro i
  rw [hilbertBurchCofactors_map318, hmap]

end PfaffianDescent
