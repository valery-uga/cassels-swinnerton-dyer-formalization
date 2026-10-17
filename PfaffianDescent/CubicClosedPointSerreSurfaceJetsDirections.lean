import PfaffianDescent.CubicClosedPointSerreSurfaceJetsTaylor
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open MvPolynomial TrivSqZeroExt
namespace PfaffianDescent
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

/-- The two free coordinates give basis vectors; the pivot coordinate
cancels the gradient, and the normalized coordinate has zero direction. -/
def cubicClosedPointSerreSurfaceJets_row
    (i : Fin 4) (a : Fin 3 → K) (k : Fin 3) : Fin 4 → Fin 2 → K :=
  Fin.insertNth i 0 (Fin.insertNth k
    (fun t => -a (k.succAbove t) / a k) (fun t => Pi.single t 1))

@[simp] theorem cubicClosedPointSerreSurfaceJets_row_diag
    (i : Fin 4) (a : Fin 3 → K) (k : Fin 3) :
    cubicClosedPointSerreSurfaceJets_row i a k i = 0 := by
  simp [cubicClosedPointSerreSurfaceJets_row]

@[simp] theorem cubicClosedPointSerreSurfaceJets_row_free
    (i : Fin 4) (a : Fin 3 → K) (k : Fin 3) (t : Fin 2) :
    cubicClosedPointSerreSurfaceJets_row i a k (i.succAbove (k.succAbove t)) =
      Pi.single t 1 := by
  simp [cubicClosedPointSerreSurfaceJets_row]

theorem cubicClosedPointSerreSurfaceJets_row_surjective
    (i : Fin 4) (a : Fin 3 → K) (k : Fin 3) :
    Function.Surjective (Fintype.linearCombination K
      (cubicClosedPointSerreSurfaceJets_row i a k)) := by
  classical
  intro z
  let f : Fin 2 → Fin 4 := fun t => i.succAbove (k.succAbove t)
  refine ⟨Pi.single (f 0) (z 0) + Pi.single (f 1) (z 1), ?_⟩
  rw [map_add]
  have hs (t : Fin 2) :
      Fintype.linearCombination K (cubicClosedPointSerreSurfaceJets_row i a k)
        (Pi.single (f t) (z t)) = z t • Pi.single t 1 := by
    simp [Fintype.linearCombination_apply, Pi.single_apply, f]
  rw [hs, hs]
  funext t
  fin_cases t <;> simp

/-- The actual normalized row annihilates the gradient. -/
theorem cubicClosedPointSerreSurfaceJets_row_gradient_zero
    (i : Fin 4) (g : Fin 4 → K) (k : Fin 3)
    (hk : g (i.succAbove k) ≠ 0) :
    ∑ j : Fin 4, g j •
      cubicClosedPointSerreSurfaceJets_row i (fun r => g (i.succAbove r)) k j = 0 := by
  classical
  rw [Fin.sum_univ_succAbove _ i]
  simp only [cubicClosedPointSerreSurfaceJets_row_diag, smul_zero, zero_add]
  simp only [cubicClosedPointSerreSurfaceJets_row, Fin.insertNth_apply_succAbove]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  funext t
  simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  fin_cases t <;> simp

end PfaffianDescent
