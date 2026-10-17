import PfaffianDescent.ActualMatchingQuadraticLineIdeal
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.MatchingCoordinateUnionScheme

/-! SOURCE ONLY, UNVERIFIED. The actual quadratic line scheme lies in the
SAME original ground cubic after extending it to the derived E. Containment
is descended by faithful flatness, not assumed. Ground union descent and
the original quadratic-secant method remain separate obligations. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalCubic_mem_matchingProjectorLineIdeal
    (B : Basis (Fin 4) K (Fin 4 → K))
    (F : MvPolynomial (Fin 4) K)
    (h01 : coordinateLineRestriction (linearSubstitution (basisCoordinateMatrix B) F) = 0) :
    F ∈ (projectorLineIdeal (matchingEdgeProjectorMatrix B)).toIdeal := by
  rw [projectorLineIdeal_eq_originalMatchingLine B]
  have hmem : linearSubstitution (basisCoordinateMatrix B) F ∈
      (coordinateMatchingLineIdeal (K := K) false).toIdeal :=
    (coordinateMatchingLineRestriction_zero_iff_mem false _).mp h01
  have h := Ideal.mem_map_of_mem
    (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom hmem
  let e := linearSubstitutionEquiv (basisCoordinateMatrix B) (basisCoordinateMatrix_isUnit B)
  change e.symm (e F) ∈ _ at h
  simpa only [AlgEquiv.symm_apply_apply] using h

theorem actualMatching_quadratic_line_in_original_cubic
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
      ∃ I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E),
        I.toIdeal.map (MvPolynomial.map E.val.toRingHom) =
          (coordinateMatchingLineIdeal (K := K) false).toIdeal.map
            (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom ∧
        ∃ hContain : (equationIdeal (MvPolynomial.map (algebraMap k E) F)
          (hF.map (algebraMap k E))).toIdeal ≤ I.toIdeal,
          ∃ c : scheme I ⟶ hypersurface (MvPolynomial.map (algebraMap k E) F)
              (hF.map (algebraMap k E)),
            IsClosedImmersion c ∧
            c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
              (hF.map (algebraMap k E))) = quotientProjMap I := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP⟩ :=
    actualMatching_projector_quadratic_field full p v hs l hl pi a f ha hU
  let I := projectorLineIdeal P
  let FE := MvPolynomial.map (algebraMap k E) F
  let FK := MvPolynomial.map (algebraMap k K) F
  have hmap : I.toIdeal.map (MvPolynomial.map (algebraMap E K)) =
      (projectorLineIdeal (matchingEdgeProjectorMatrix B)).toIdeal := by
    change (projectorLineIdeal P).toIdeal.map (MvPolynomial.map E.val.toRingHom) = _
    rw [projectorLineIdeal_baseChange, hP]
  have h01 : coordinateLineRestriction (linearSubstitution (basisCoordinateMatrix B) FK) = 0 :=
    (cubic_contains_matching_lines_of_skew_matrix a f ha hf _
      (linearSubstitution_homogeneous _ (hF.map (algebraMap k K))) hvan).1
  have hFK : FK ∈ (projectorLineIdeal (matchingEdgeProjectorMatrix B)).toIdeal :=
    originalCubic_mem_matchingProjectorLineIdeal B FK h01
  have hFE : FE ∈ I.toIdeal := by
    rw [← PfaffianDescent.mvPolynomial_comap_map_coefficientExtension
      (k := E) (K := K) I.toIdeal]
    change MvPolynomial.map (algebraMap E K) FE ∈
      I.toIdeal.map (MvPolynomial.map (algebraMap E K))
    rw [hmap]
    have hcoeff : (algebraMap E K).comp (algebraMap k E) = algebraMap k K := by
      ext z
      rfl
    have hFEK : MvPolynomial.map (algebraMap E K) FE = FK := by
      dsimp only [FE, FK]
      rw [MvPolynomial.map_map, hcoeff]
    rw [hFEK]
    exact hFK
  have hContain : (equationIdeal FE (hF.map (algebraMap k E))).toIdeal ≤ I.toIdeal := by
    apply Ideal.span_le.mpr
    rintro q rfl
    exact hFE
  let c := schemeQuotientMap (equationIdeal FE (hF.map (algebraMap k E))) I hContain
  letI : IsClosedImmersion c := schemeQuotientMap_closedImmersion _ _ _
  refine ⟨E, hFD, hdeg, hGal, hE, I, ?_, hContain, c, inferInstance, ?_⟩
  · change I.toIdeal.map (MvPolynomial.map (algebraMap E K)) = _
    rw [hmap, projectorLineIdeal_eq_originalMatchingLine B]
  · exact schemeQuotientMap_comp_quotientProjMap _ _ _

end PfaffianDescent.QuarticNet
