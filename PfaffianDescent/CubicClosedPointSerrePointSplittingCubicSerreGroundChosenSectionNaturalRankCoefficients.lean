import PfaffianDescent.SerreActualCanonicalBasisMatrixReindex

noncomputable section
open Module
namespace PfaffianDescent
universe u v w

/-- The literal normalized fixed-rank coefficient formula is the same formula
on the actual natural rank index of the canonical basis. -/
theorem pointSplittingCubicSerreGroundChosenSection_naturalRank_coefficients
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = n)
    (b : Basis (Fin n) K V) {R : Type w} [CommRing R]
    (φ : K →+* R) (oldcoeff : Fin n → R) (u : R)
    (newcoeff : Fin (finrank K V) → R)
    (h : ∀ j, newcoeff ((finCongr hn).symm j) =
      u * ((((finBasisOfFinrankEq K V hn).toMatrix b).map φ).mulVec oldcoeff) j) :
    ∀ i, newcoeff i =
      u * ((((finBasis K V).toMatrix b).map φ).mulVec oldcoeff) i := by
  intro i
  have hi := h ((finCongr hn) i)
  rw [Equiv.symm_apply_apply] at hi
  have hm : (((finBasisOfFinrankEq K V hn).toMatrix b).map φ) ((finCongr hn) i) =
      (((finBasis K V).toMatrix b).map φ) i := by
    funext j
    simp only [Matrix.map_apply, serreActualCanonicalBasisMatrix_reindex,
      Equiv.symm_apply_apply]
  exact hi.trans (congrArg (fun row => u * dotProduct row oldcoeff) hm)

end PfaffianDescent
