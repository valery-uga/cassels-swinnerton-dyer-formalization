import PfaffianDescent.ActualMatchingProjectorCoefficientField
import PfaffianDescent.BasisMatchingProjectorActualLineIdeal

/-! SOURCE ONLY, UNVERIFIED. Field-of-definition equality for the WHOLE
actual original line ideal, over the SAME quadratic edge field. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]

theorem actualMatching_quadratic_line_ideal
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E),
        I.toIdeal.map (MvPolynomial.map E.val.toRingHom) =
          (coordinateMatchingLineIdeal (K := K) false).toIdeal.map
            (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom := by
  dsimp only
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP⟩ :=
    actualMatching_projector_quadratic_field full p v hs l hl pi a f ha hU
  refine ⟨E, hFD, hdeg, hGal, hE, projectorLineIdeal P, ?_⟩
  rw [projectorLineIdeal_baseChange, hP, projectorLineIdeal_eq_originalMatchingLine]

end PfaffianDescent.QuarticNet
