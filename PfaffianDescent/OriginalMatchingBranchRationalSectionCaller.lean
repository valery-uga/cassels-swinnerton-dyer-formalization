import PfaffianDescent.QuadraticSkewOriginalMatchingBranchRationality
import PfaffianDescent.OriginalMatchingActualQuadraticLineSecantData

/-! SOURCE ONLY. The original matching branch supplies both rationality and
an explicit ground section, using the same internally descended whole ideal.
No rationality-to-point theorem or extra geometric bundle is assumed. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalMatchingBranch_original_cubic_rational_and_section
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
    Scheme.IsRationalOver (hypersurfaceToBase F hF) ∧
      ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  have hRational := originalMatchingBranch_original_cubic_isRationalOver
    full p v hs l hl pi a f ha hf hU F hF hF₀ hvan
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
      J, hJE, hJK, hUnion, hContain, cGround, hcGround, hAmbientGround⟩ :=
    actualMatching_ground_union_in_original_cubic full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  obtain ⟨C, hC, e, heBase, c, hc, hcAmbient, q, hqBase, hqCubic, s, hsBase⟩ :=
    originalMatching_groundUnion_actualQuadraticLine_and_secant E hdeg P B hP F hF J hJE hContain
  exact ⟨hRational, s, hsBase⟩

end PfaffianDescent.QuarticNet
