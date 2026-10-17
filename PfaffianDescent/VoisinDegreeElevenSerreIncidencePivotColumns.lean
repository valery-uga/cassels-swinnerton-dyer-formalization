import PfaffianDescent.VoisinDegreeElevenSerreIncidencePivotSplit
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-! # Internal completion of an actual six-column pivot to nine coordinates -/
noncomputable section
namespace PfaffianDescent
universe u
variable {R : Type u} [CommRing R]

/-- The three remaining columns and a full coordinate permutation are chosen
internally from the actual six-column embedding. -/
theorem serreSixColumnEmbedding_exists_completion (m : Fin 6 ↪ Fin 9) :
    ∃ e : (Fin 6 ⊕ Fin 3) ≃ Fin 9, ∀ i, e (Sum.inl i) = m i := by
  classical
  letI : DecidablePred (Set.range m) := Classical.decPred _
  have hcard : Fintype.card ((Set.range m)ᶜ : Set (Fin 9)) = 3 := by
    rw [Fintype.card_compl_set, Fintype.card_range]
    rfl
  let a := Equiv.ofInjective m m.injective
  let c := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨(Equiv.sumCongr a c).trans (Equiv.sumCompl (Set.range m)), ?_⟩
  intro i
  rfl

abbrev serrePivotEvaluationReindexed
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) :=
  (serrePivotEvaluation P Q).submatrix id e.symm
abbrev serrePivotKernelFrameReindexed
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) :=
  (serrePivotKernelFrame P Q).submatrix e.symm id
abbrev serrePivotKernelRetractionReindexed (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) :=
  (serrePivotKernelRetraction (R := R)).submatrix id e.symm
abbrev serrePivotEvaluationSplittingReindexed
    (P : Matrix (Fin 6) (Fin 6) R) (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) :=
  (serrePivotEvaluationSplitting P).submatrix e.symm id

theorem serrePivotReindexedKernel_vanishes
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) (hP : IsUnit P.det) :
    serrePivotEvaluationReindexed P Q e * serrePivotKernelFrameReindexed P Q e = 0 := by
  rw [Matrix.submatrix_mul_equiv, serrePivotKernelFrame_vanishes P Q hP]
  rfl

theorem serrePivotReindexedKernel_retracts
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) :
    serrePivotKernelRetractionReindexed (R := R) e * serrePivotKernelFrameReindexed P Q e = 1 := by
  rw [Matrix.submatrix_mul_equiv, serrePivotKernelFrame_retracts]
  rfl

theorem serrePivotReindexedKernel_decomposition
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (e : (Fin 6 ⊕ Fin 3) ≃ Fin 9) (hP : IsUnit P.det) :
    serrePivotKernelFrameReindexed P Q e * serrePivotKernelRetractionReindexed (R := R) e +
      serrePivotEvaluationSplittingReindexed P e * serrePivotEvaluationReindexed P Q e = 1 := by
  have hM := Matrix.submatrix_mul_equiv (serrePivotKernelFrame P Q)
    (serrePivotKernelRetraction (R := R)) e.symm (Equiv.refl (Fin 3)) e.symm
  have hD := Matrix.submatrix_mul_equiv (serrePivotEvaluationSplitting P)
    (serrePivotEvaluation P Q) e.symm (Equiv.refl (Fin 6)) e.symm
  change (serrePivotKernelFrame P Q).submatrix e.symm id *
    (serrePivotKernelRetraction (R := R)).submatrix id e.symm = _ at hM
  change (serrePivotEvaluationSplitting P).submatrix e.symm id *
    (serrePivotEvaluation P Q).submatrix id e.symm = _ at hD
  change (serrePivotKernelFrame P Q).submatrix e.symm id *
    (serrePivotKernelRetraction (R := R)).submatrix id e.symm +
    (serrePivotEvaluationSplitting P).submatrix e.symm id *
    (serrePivotEvaluation P Q).submatrix id e.symm = 1
  rw [hM, hD]
  have h := congrArg (fun T => T.submatrix e.symm e.symm)
    (serrePivotKernelFrame_decomposition P Q hP)
  simpa only [Matrix.submatrix_add, Pi.add_apply, Matrix.submatrix_one_equiv] using h

/-- The actual invertible minor internally supplies all three split matrices
in the original nine-coordinate order. -/
theorem serreEvaluationMatrix_exists_split_of_unit_minor
    (A : Matrix (Fin 6) (Fin 9) R) (m : Fin 6 ↪ Fin 9)
    (hm : IsUnit (A.submatrix id m).det) :
    ∃ (M : Matrix (Fin 9) (Fin 3) R) (N : Matrix (Fin 3) (Fin 9) R)
      (D : Matrix (Fin 9) (Fin 6) R),
      A * M = 0 ∧ N * M = 1 ∧ M * N + D * A = 1 := by
  obtain ⟨e, he⟩ := serreSixColumnEmbedding_exists_completion m
  let P := A.submatrix id m
  let Q := A.submatrix id (fun j => e (Sum.inr j))
  have hA : A = serrePivotEvaluationReindexed P Q e := by
    ext i j
    obtain ⟨k, rfl⟩ := e.surjective j
    rcases k with k | k
    · change A i (e (Sum.inl k)) =
        serrePivotEvaluation P Q i (e.symm (e (Sum.inl k)))
      rw [Equiv.symm_apply_apply]
      change A i (e (Sum.inl k)) = A i (m k)
      rw [he]
    · change A i (e (Sum.inr k)) =
        serrePivotEvaluation P Q i (e.symm (e (Sum.inr k)))
      rw [Equiv.symm_apply_apply]
      rfl
  refine ⟨serrePivotKernelFrameReindexed P Q e,
    serrePivotKernelRetractionReindexed e, serrePivotEvaluationSplittingReindexed P e, ?_, ?_, ?_⟩
  · rw [hA]
    exact serrePivotReindexedKernel_vanishes P Q e hm
  · exact serrePivotReindexedKernel_retracts P Q e
  · rw [hA]
    exact serrePivotReindexedKernel_decomposition P Q e hm

end PfaffianDescent
