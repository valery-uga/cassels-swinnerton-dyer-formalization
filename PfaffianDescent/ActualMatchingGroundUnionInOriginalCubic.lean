import PfaffianDescent.MatchingProjectorIntersectionBaseChange
import PfaffianDescent.BasisMatchingProjectorWholeUnionIdeal
import PfaffianDescent.ActualMatchingQuadraticLineKernelBasis
import PfaffianDescent.MatchingCoordinateUnionScheme
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat

/-! SOURCE ONLY, UNVERIFIED. Exact descended WHOLE union, retaining the
SAME original cubic and inverse-GL ambient embedding. E, the projector,
rank-two kernels, and the ground intersection ideal are derived internally.
No intersection/base-change, line-containment or descent certificate input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalCubic_mem_matchingProjectorIntersection
    (B : Basis (Fin 4) K (Fin 4 → K))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (hvan : ∀ r, aeval (tangentDualPoint
      (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix B) F) = 0) :
    F ∈ (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal := by
  rw [matchingProjectorIntersectionIdeal_eq_originalMatchingUnion B]
  have hmem : linearSubstitution (basisCoordinateMatrix B) F ∈
      (coordinateMatchingUnionIdeal (K := K)).toIdeal := by
    apply equationIdeal_le_matchingUnion_of_skew_double_points a f ha hf _
      (linearSubstitution_homogeneous _ hF) hvan
    exact Ideal.subset_span (by simp)
  have h := Ideal.mem_map_of_mem
    (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom hmem
  let e := linearSubstitutionEquiv (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B)
  change e.symm (e F) ∈ _ at h
  simpa only [AlgEquiv.symm_apply_apply, coordinateMatchingUnionIdeal,
    HomogeneousIdeal.toIdeal_inf] using h

/-- Literal matching branch: the union of the two conjugate skew lines
is an actual ground closed subscheme of the ORIGINAL cubic. The extension
identities concern ideals, so they retain the original scheme structure. -/
theorem actualMatching_ground_union_in_original_cubic
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
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = matchingEdgeProjectorMatrix B ∧
        finrank E (LinearMap.ker (1 - P).mulVecLin) = 2 ∧
        finrank E (LinearMap.ker P.mulVecLin) = 2 ∧
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (matchingProjectorIntersectionIdeal P).toIdeal ∧
          J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
            (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal ∧
          J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
            (coordinateMatchingUnionIdeal (K := K)).toIdeal.map
              (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom ∧
          ∃ hContain : (equationIdeal F hF).toIdeal ≤ J.toIdeal,
            ∃ c : scheme J ⟶ hypersurface F hF,
              IsClosedImmersion c ∧
              c ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap J := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hBasis,
      hOtherKernel, hOtherBasis, J, hJ⟩ :=
    actualMatching_ground_intersection_with_line_kernel full p v hs l hl pi a f ha hU
  have hJE : J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
      (matchingProjectorIntersectionIdeal P).toIdeal := hJ
  have hJK : J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
      (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal := by
    have h := matchingGroundIntersection_extension_to_original (K := K) J P hJE
    change J.toIdeal.map (MvPolynomial.map (algebraMap k K)) =
      (matchingProjectorIntersectionIdeal (P.map E.val.toRingHom)).toIdeal at h
    simpa only [hP] using h
  have hFK : MvPolynomial.map (algebraMap k K) F ∈
      (matchingProjectorIntersectionIdeal (matchingEdgeProjectorMatrix B)).toIdeal :=
    originalCubic_mem_matchingProjectorIntersection B _
      (hF.map (algebraMap k K)) a f ha hf hvan
  have hFJ : F ∈ J.toIdeal := by
    rw [← PfaffianDescent.mvPolynomial_comap_map_coefficientExtension
      (k := k) (K := K) J.toIdeal]
    change MvPolynomial.map (algebraMap k K) F ∈
      J.toIdeal.map (MvPolynomial.map (algebraMap k K))
    rw [hJK]
    exact hFK
  have hContain : (equationIdeal F hF).toIdeal ≤ J.toIdeal := by
    apply Ideal.span_le.mpr
    rintro q rfl
    exact hFJ
  let c := schemeQuotientMap (equationIdeal F hF) J hContain
  have hc : IsClosedImmersion c :=
    schemeQuotientMap_closedImmersion (equationIdeal F hF) J hContain
  refine ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
    J, hJE, hJK, ?_, hContain, c, hc, ?_⟩
  · rw [hJK, matchingProjectorIntersectionIdeal_eq_originalMatchingUnion B]
    rfl
  · exact schemeQuotientMap_comp_quotientProjMap _ _ _

end PfaffianDescent.QuarticNet
