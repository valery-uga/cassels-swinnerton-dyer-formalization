import PfaffianDescent.ActualOriginalMatchingQuadraticLinePair
import PfaffianDescent.ScaledRelabeledFrameTangent

/-! SOURCE ONLY / UNVERIFIED. Preserve the canonical quadratic field while
identifying the supplied matched line IDEALS in the same ambient coordinates.
Arbitrary column scalars must not replace the canonical edge-sum field. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The supplied matching lines are literally the base changes of the pair
already constructed over ONE canonical quadratic field. The equality is of
polynomial ideals, including their original ambient embedding equations. -/
def OriginalMatchingQuadraticLinePairOnSuppliedFrame
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (supplied : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (V : Fin 4 → Fin 4 → AlgebraicClosure k) : Prop :=
  ∃ pi : Equiv.Perm (Fin 4),
    (∀ r s, V (pi r) (pi s) ≠ 0 ↔ QuarticNet.coordinateMatchingAdj r s) ∧
    ∃ B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k),
      OriginalMatchingQuadraticLinePairObjects F hF B ∧
      ∀ side : Bool,
        (QuarticNet.coordinateMatchingLineIdeal (K := AlgebraicClosure k) side).toIdeal.map
          (linearSubstitution (QuarticNet.basisCoordinateMatrix
            (supplied.reindex pi.symm))⁻¹).toRingHom =
        (QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector
          (QuarticNet.matchingEdgeProjectorMatrix B) side)).toIdeal

namespace QuarticNet
variable {K : Type u} [Field K]

/-- Independent nonzero column scalars cancel against dual basis scalars. -/
theorem matchingEdgeProjectorMatrix_unitsSMul
    (B : Basis (Fin 4) K (Fin 4 → K)) (c : Fin 4 → Kˣ) :
    matchingEdgeProjectorMatrix (B.unitsSMul c) = matchingEdgeProjectorMatrix B := by
  ext m n
  simp only [matchingEdgeProjectorMatrix, Basis.unitsSMul_apply,
    Basis.repr_unitsSMul, Units.smul_def, Pi.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  field_simp [(c 0).ne_zero, (c 1).ne_zero] <;> ring

/-- Relabel the supplied frame by the SAME matching edges, then all column
scalars cancel. The original ambient coordinate indices m,n never move. -/
theorem matchingEdgeProjectorMatrix_scaled_frame_reindex
    (B : Basis (Fin 4) K (Fin 4 → K)) (rho pi : Equiv.Perm (Fin 4))
    (c : Fin 4 → Kˣ) :
    matchingEdgeProjectorMatrix
      ((scaledRelabeledFrame B rho c).reindex (pi.trans rho.symm).symm) =
    matchingEdgeProjectorMatrix (B.reindex pi.symm) := by
  have hBasis : (scaledRelabeledFrame B rho c).reindex (pi.trans rho.symm).symm =
      (B.reindex pi.symm).unitsSMul (fun r => c (rho.symm (pi r))) := by
    apply DFunLike.ext
    intro r
    simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.trans_apply,
      scaledRelabeledFrame_column, Equiv.apply_symm_apply, Basis.unitsSMul_apply,
      Units.smul_def]
  rw [hBasis, matchingEdgeProjectorMatrix_unitsSMul]

/-- INTERNAL transport adapter. The actual component caller below DERIVES
hBasis and hV from the supplied support set and literal embedding squares;
its final statement takes no frame or graph comparison certificate. -/
theorem originalMatching_pair_on_supplied_frame_of_actual_comparison
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B supplied : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (U V : Fin 4 → Fin 4 → AlgebraicClosure k)
    (rho : Equiv.Perm (Fin 4)) (c : Fin 4 → (AlgebraicClosure k)ˣ)
    (epsilon : Fin 4 → AlgebraicClosure k) (hepsilon : ∀ r, epsilon r ≠ 0)
    (hBasis : supplied = scaledRelabeledFrame B rho c)
    (hV : V = suppliedFrameTangent U rho (fun r => (c r : AlgebraicClosure k)) epsilon)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0)
    (hGeometry : OriginalMatchingQuadraticLineGeometryAt F hF B
      (rescaleTangentDirections l U)) :
    OriginalMatchingQuadraticLinePairOnSuppliedFrame F hF supplied V := by
  obtain ⟨pi, hEdges, hObjects⟩ := hGeometry
  let piSupplied := pi.trans rho.symm
  refine ⟨piSupplied, ?_, B.reindex pi.symm, hObjects, ?_⟩
  · intro r s
    have hVEdge : V (piSupplied r) (piSupplied s) ≠ 0 ↔ U (pi r) (pi s) ≠ 0 := by
      rw [hV]
      simpa only [piSupplied, Equiv.trans_apply, Equiv.apply_symm_apply] using
        not_congr (suppliedFrameTangent_zero_iff U rho (fun r => (c r : AlgebraicClosure k))
          epsilon (fun r => (c r).ne_zero) hepsilon (piSupplied r) (piSupplied s))
    exact hVEdge.trans ((rescaleTangentDirections_nonzero U l hl (pi r) (pi s)).symm.trans
      (hEdges r s))
  · have hProjector : matchingEdgeProjectorMatrix (supplied.reindex piSupplied.symm) =
        matchingEdgeProjectorMatrix (B.reindex pi.symm) := by
      rw [hBasis]
      exact matchingEdgeProjectorMatrix_scaled_frame_reindex B rho pi c
    intro side
    cases side
    · rw [← projectorLineIdeal_eq_originalMatchingLine, hProjector]
      rfl
    · rw [← projectorComplementLineIdeal_eq_originalMatchingLine, hProjector]
      rfl

end QuarticNet
end PfaffianDescent
