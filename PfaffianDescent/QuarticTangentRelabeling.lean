import PfaffianDescent.QuarticConjugateJets
import PfaffianDescent.QuarticTangentGraph

/-!
# Relabeling the matching and four-cycle tangent configurations
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

variable {K : Type*} [Field K]

noncomputable def tangentRelabel (U : Fin 4 → Fin 4 → K)
    (π : Equiv.Perm (Fin 4)) : Fin 4 → Fin 4 → K :=
  fun i j => U (π i) (π j)

theorem tangentRelabel_vanishing (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (π : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hF : ∀ i, aeval (tangentDualPoint U i)
      (linearSubstitution (basisCoordinateMatrix b) F) = 0) :
    ∀ i, aeval (tangentDualPoint (tangentRelabel U π) i)
      (linearSubstitution (basisCoordinateMatrix (b.reindex π.symm)) F) = 0 := by
  intro i
  have hx : (fun m => ∑ j, algebraMap K (DualNumber K)
      (basisCoordinateMatrix (b.reindex π.symm) m j) *
        tangentDualPoint (tangentRelabel U π) i j) =
      fun m => ∑ j, algebraMap K (DualNumber K) (basisCoordinateMatrix b m j) *
        tangentDualPoint U (π i) j := by
    funext m
    have ht (j : Fin 4) : tangentDualPoint (tangentRelabel U π) i j =
        tangentDualPoint U (π i) (π j) := by
      simp [tangentDualPoint, tangentRelabel]
    simp only [basisCoordinateMatrix, Basis.reindex_apply, Equiv.symm_symm, ht]
    exact Equiv.sum_comp π (fun j => algebraMap K (DualNumber K) (b j m) *
      tangentDualPoint U (π i) j)
  rw [aeval_linearSubstitution, hx, ← aeval_linearSubstitution]
  exact hF (π i)

theorem matching_relabel (U : Fin 4 → Fin 4 → K)
    (hskew : ∀ i j, U i j = -U j i)
    (h : matchingPattern (nonzeroEdge (U 0 1)) (nonzeroEdge (U 0 2))
      (nonzeroEdge (U 0 3)) (nonzeroEdge (U 1 2)) (nonzeroEdge (U 1 3))
      (nonzeroEdge (U 2 3))) :
    ∃ π : Equiv.Perm (Fin 4),
      tangentRelabel U π 0 1 ≠ 0 ∧ tangentRelabel U π 2 3 ≠ 0 ∧
      tangentRelabel U π 0 2 = 0 ∧ tangentRelabel U π 0 3 = 0 ∧
      tangentRelabel U π 1 2 = 0 ∧ tangentRelabel U π 1 3 = 0 := by
  simp only [matchingPattern, nonzeroEdge, decide_eq_true_eq,
    decide_eq_false_iff_not, not_not] at h
  rcases h with h | h | h
  · exact ⟨Equiv.refl _, h⟩
  · refine ⟨Equiv.swap 1 2, ?_⟩
    simpa [tangentRelabel, Equiv.swap_apply_def, hskew 2 1] using h
  · refine ⟨Equiv.swap 1 3, ?_⟩
    rcases h with ⟨hc, hd, ha, hb, he, hf⟩
    simp [tangentRelabel, Equiv.swap_apply_def, hskew 3 2, hskew 3 1,
      hskew 2 1, ha, hb, he, hf, hc, hd]

theorem fourCycle_relabel (U : Fin 4 → Fin 4 → K)
    (hskew : ∀ i j, U i j = -U j i)
    (h : matchingPattern (!(nonzeroEdge (U 0 1))) (!(nonzeroEdge (U 0 2)))
      (!(nonzeroEdge (U 0 3))) (!(nonzeroEdge (U 1 2)))
      (!(nonzeroEdge (U 1 3))) (!(nonzeroEdge (U 2 3)))) :
    ∃ π : Equiv.Perm (Fin 4),
      tangentRelabel U π 0 1 = 0 ∧ tangentRelabel U π 2 3 = 0 ∧
      tangentRelabel U π 0 2 ≠ 0 ∧ tangentRelabel U π 0 3 ≠ 0 ∧
      tangentRelabel U π 1 2 ≠ 0 ∧ tangentRelabel U π 1 3 ≠ 0 := by
  simp only [matchingPattern, nonzeroEdge, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h
  rcases h with h | h | h
  · exact ⟨Equiv.refl _, h⟩
  · refine ⟨Equiv.swap 1 2, ?_⟩
    simpa [tangentRelabel, Equiv.swap_apply_def, hskew 2 1] using h
  · refine ⟨Equiv.swap 1 3, ?_⟩
    rcases h with ⟨hc, hd, ha, hb, he, hf⟩
    simp [tangentRelabel, Equiv.swap_apply_def, hskew 3 2, hskew 3 1,
      hskew 2 1, ha, hb, he, hf, hc, hd]

end QuarticNet
end PfaffianDescent
