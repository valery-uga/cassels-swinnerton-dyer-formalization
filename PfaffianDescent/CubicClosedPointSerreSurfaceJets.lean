import PfaffianDescent.CubicClosedPointSerreSurfaceJetsDirections
import PfaffianDescent.CubicClosedPointSerreSurfaceJetsGradient

/-! # Native two-dimensional surface jets at three coordinate vertices -/
noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Smoothness and the three actual vertex equations construct normalized
full surface tangent directions and literal square-zero points on the cubic.
The tangent-spanning and equation-vanishing facts are conclusions. -/
theorem cubicClosedPointSerreSurfaceJets_exists_native
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hvertices : ∀ i : Fin 3,
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i.castSucc) p = 0) :
    ∃ U : Fin 4 → Fin 4 → (Fin 2 → K),
      (∀ i, U i i = 0) ∧
      (∀ i : Fin 3, Function.Surjective (Fintype.linearCombination K (U i.castSucc))) ∧
      (∀ i : Fin 3, aeval (cubicSurfaceCoordinateJet U i.castSucc) p = 0) := by
  classical
  have hgrad : ∀ i : Fin 3, ∃ k : Fin 3,
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i.castSucc)
        (pderiv (i.castSucc.succAbove k) p) ≠ 0 := by
    intro i
    obtain ⟨j, hji, hj⟩ := cubicClosedPointSerreSurfaceJets_exists_nonzero_gradient
      p hp hp0 i.castSucc (hvertices i)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact ⟨k, hj⟩
  choose k hk using hgrad
  let k₄ : Fin 4 → Fin 3 := Fin.lastCases 0 k
  let g : Fin 4 → Fin 4 → K := fun i j =>
    aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) (pderiv j p)
  let U : Fin 4 → Fin 4 → Fin 2 → K := fun i =>
    cubicClosedPointSerreSurfaceJets_row i (fun r => g i (i.succAbove r)) (k₄ i)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro i
    exact cubicClosedPointSerreSurfaceJets_row_diag i _ _
  · intro i
    exact cubicClosedPointSerreSurfaceJets_row_surjective i.castSucc _ _
  · intro i
    have hki : g i.castSucc (i.castSucc.succAbove (k₄ i.castSucc)) ≠ 0 := by
      simpa only [g, k₄, Fin.lastCases_castSucc] using hk i
    have hsum : ∑ j : Fin 4, g i.castSucc j • U i.castSucc j = 0 :=
      cubicClosedPointSerreSurfaceJets_row_gradient_zero i.castSucc (g i.castSucc)
        (k₄ i.castSucc) hki
    change aeval (fun j => inl (cubicClosedPointSerreSurfaceJets_vertex
      (K := K) i.castSucc j) + inr (U i.castSucc j)) p = 0
    rw [cubicClosedPointSerreSurfaceJets_taylor, hvertices i]
    change inl (0 : K) + inr (∑ j : Fin 4, g i.castSucc j • U i.castSucc j) = 0
    rw [hsum]
    simp

end PfaffianDescent
