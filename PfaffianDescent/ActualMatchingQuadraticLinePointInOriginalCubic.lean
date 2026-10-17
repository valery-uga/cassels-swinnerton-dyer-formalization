import PfaffianDescent.MatchingLineActualCoordinatePoint
import PfaffianDescent.ActualMatchingGroundUnionInOriginalCubic

/-! SOURCE ONLY, UNVERIFIED. Compose the SAME derived matching E/P/J
with genuine P1 identification and original cubic containment. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualMatching_quadratic_line_point_in_original_cubic
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
        ∃ C : Basis (Fin 4) E (Fin 4 → E),
          matchingEdgeProjectorMatrix C = P ∧
          Nonempty (scheme (projectorLineIdeal P) ≅ Proj (homogeneousSubmodule (Fin 2) E)) ∧
          ∃ c : scheme (projectorLineIdeal P) ⟶
              hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
            IsClosedImmersion c ∧
            c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
              (hF.map (algebraMap k E))) = quotientProjMap (projectorLineIdeal P) ∧
            ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
              q ≫ toBase (projectorLineIdeal P) = 𝟙 _ ∧
              (q ≫ c) ≫ hypersurfaceToBase (MvPolynomial.map (algebraMap k E) F)
                (hF.map (algebraMap k E)) = 𝟙 _ ∧
              C 0 ≠ 0 ∧ F.eval₂ (algebraMap k E) (C 0) = 0 := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
      J, hJE, hJK, hUnion, hContainGround, cGround, hClosedGround, hAmbientGround⟩ :=
    actualMatching_ground_union_in_original_cubic full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  letI : IsGalois k E := hGal
  obtain ⟨C, hC, e, heBase, heAmbient⟩ := intermediateMatchingLine_projectiveLine_iso E P B hP
  let FE := MvPolynomial.map (algebraMap k E) F
  have hFJ : F ∈ J.toIdeal := hContainGround (Ideal.subset_span (by simp))
  have hFE : FE ∈ (projectorLineIdeal P).toIdeal := by
    have h := Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap k E)) hFJ
    rw [hJE] at h
    exact h.1
  have hContain : (equationIdeal FE (hF.map (algebraMap k E))).toIdeal ≤
      (projectorLineIdeal P).toIdeal := by
    apply Ideal.span_le.mpr
    rintro q rfl
    exact hFE
  let c := schemeQuotientMap (equationIdeal FE (hF.map (algebraMap k E)))
    (projectorLineIdeal P) hContain
  letI : IsClosedImmersion c := schemeQuotientMap_closedImmersion _ _ _
  have hPoint : ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
      q ≫ toBase (projectorLineIdeal P) = 𝟙 _ := by
    simpa only [hC] using matchingProjectorLine_has_actual_firstBasisPoint C
  obtain ⟨q, hqP⟩ := hPoint
  have hEval : FE.eval₂ (algebraMap E E) (C 0) = 0 := by
    apply matchingProjectorLineIdeal_le_firstBasisCoordinateKernel C
    simpa only [hC] using hFE
  have hOriginalEval : F.eval₂ (algebraMap k E) (C 0) = 0 := by
    simpa only [FE, MvPolynomial.eval₂_map, algebraMap_self, RingHom.id_comp] using hEval
  have hqCubic : (q ≫ c) ≫ hypersurfaceToBase FE (hF.map (algebraMap k E)) = 𝟙 _ := by
    change (q ≫ schemeQuotientMap (equationIdeal FE (hF.map (algebraMap k E)))
      (projectorLineIdeal P) hContain) ≫ toBase (equationIdeal FE (hF.map (algebraMap k E))) = _
    rw [Category.assoc, schemeQuotientMap_toBase]
    exact hqP
  refine ⟨E, hFD, hdeg, hGal, hE, P, hP, C, hC, ⟨e⟩,
    c, inferInstance, ?_, q, hqP, hqCubic, C.linearIndependent.ne_zero 0, hOriginalEval⟩
  exact schemeQuotientMap_comp_quotientProjMap _ _ _

end PfaffianDescent.QuarticNet
