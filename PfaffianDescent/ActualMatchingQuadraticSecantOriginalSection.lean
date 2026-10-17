import PfaffianDescent.ActualMatchingQuadraticLinePointInOriginalCubic
import AllCharacteristics.CubicPolynomialCoordinates
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY, UNVERIFIED. The literal matching method: construct a
point on the derived genuine quadratic E-line in SAME original cubic,
then apply only the Chapter2 quadratic-secant residual identity. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualMatching_quadratic_secant_original_section
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint
      (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix
        ((conjugateBasis full p hs).reindex pi.symm))
        (MvPolynomial.map (algebraMap k K) F)) = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, C, hC, hP1, c, hc, hAmbient,
      q, hq, hqCubic, hC0, hFE⟩ :=
    actualMatching_quadratic_line_point_in_original_cubic
      full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  obtain ⟨y, hy, hFy⟩ := AllCharacteristics.homogeneous_cubic_degree_le_two_descent
    F hF (by omega : finrank k E ≤ 2) (C 0) hC0 hFE
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) F hF y hy hFy
  refine ⟨s, ?_⟩
  simpa using hs

end PfaffianDescent.QuarticNet
