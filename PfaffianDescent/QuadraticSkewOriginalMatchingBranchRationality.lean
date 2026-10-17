import PfaffianDescent.ActualMatchingGroundUnionInOriginalCubic
import PfaffianDescent.ActualMatchingQuadraticProjectorExchange
import PfaffianDescent.QuadraticSkewActualMatchingOriginalCubicRationality
/-! Source draft: derive all rationality-construction inputs from the actual
original matching branch, retaining its whole descended ideal. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open PfaffianDescent.QuadraticSkewRationality.SecondComposite005
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalMatchingBranch_original_cubic_isRationalOver
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hvan : ∀ r, aeval (tangentDualPoint
      (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix
        ((conjugateBasis full p hs).reindex pi.symm))
        (MvPolynomial.map (algebraMap k K) F)) = 0) :
    Scheme.IsRationalOver (hypersurfaceToBase F hF) := by
  classical
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
      J, hJE, hJK, hUnion, hContain, cGround, hcGround, hAmbientGround⟩ :=
    actualMatching_ground_union_in_original_cubic full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  letI : IsGalois k E := hGal
  obtain ⟨sigma, hNe, hSquare, hExchange, hLineExchange, hOtherExchange⟩ :=
    actualMatching_quadratic_projector_exchange full p v hs l hl pi a f ha hU E hdeg P hP
  have hFJ : F ∈ J.toIdeal := hContain (Ideal.subset_span (by simp))
  have hFE : MvPolynomial.map (algebraMap k E) F ∈
      (matchingProjectorIntersectionIdeal P).toIdeal := by
    rw [← hJE]
    exact Ideal.mem_map_of_mem _ hFJ
  exact actual_matching_original_cubic_isRationalOver E hdeg P B hP sigma
    (by change sigma ≠ 1; exact hNe) hExchange F hF hF₀ ⟨hFE.1, hFE.2⟩

end PfaffianDescent.QuarticNet
