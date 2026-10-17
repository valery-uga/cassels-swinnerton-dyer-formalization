import PfaffianDescent.ActualMatchingQuadraticLineProjectiveIso
import PfaffianDescent.MatchingLineActualCoordinatePoint
import AllCharacteristics.CubicPolynomialCoordinates
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY, UNVERIFIED. Small actual E/P/J consumer; these structural
facts are DERIVED by the public matching caller, not new final certificates.
It preserves one E/P/J extraction for line/P1/point/quadratic secant. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem matchingLine_actualPoint_of_frame
    (E : Type u) [Field E] (C : Basis (Fin 4) E (Fin 4 → E))
    (P : Matrix (Fin 4) (Fin 4) E) (hC : matchingEdgeProjectorMatrix C = P) :
    ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
      q ≫ toBase (projectorLineIdeal P) = 𝟙 _ := by
  subst P
  exact matchingProjectorLine_has_actual_firstBasisPoint C

theorem originalMatching_groundUnion_actualQuadraticLine_and_secant
    (E : IntermediateField k K) [FiniteDimensional k E]
    (hdeg : finrank k E = 2)
    (P : Matrix (Fin 4) (Fin 4) E) (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hJE : J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
      (matchingProjectorIntersectionIdeal P).toIdeal)
    (hContainGround : (equationIdeal F hF).toIdeal ≤ J.toIdeal) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E), matchingEdgeProjectorMatrix C = P ∧
      ∃ e : scheme (projectorLineIdeal P) ≅ Proj (homogeneousSubmodule (Fin 2) E),
        e.hom ≫ ambientToBase (R := E) (σ := Fin 2) = toBase (projectorLineIdeal P) ∧
        ∃ c : scheme (projectorLineIdeal P) ⟶
            hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
          IsClosedImmersion c ∧
          c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
            (hF.map (algebraMap k E))) = quotientProjMap (projectorLineIdeal P) ∧
          ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
            q ≫ toBase (projectorLineIdeal P) = 𝟙 _ ∧
            (q ≫ c) ≫ hypersurfaceToBase (MvPolynomial.map (algebraMap k E) F)
              (hF.map (algebraMap k E)) = 𝟙 _ ∧
            ∃ s : Spec (.of k) ⟶ hypersurface F hF,
              s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
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
  have hc : IsClosedImmersion c :=
    schemeQuotientMap_closedImmersion (equationIdeal FE (hF.map (algebraMap k E)))
      (projectorLineIdeal P) hContain
  have hPoint : ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal P),
      q ≫ toBase (projectorLineIdeal P) = 𝟙 _ :=
    matchingLine_actualPoint_of_frame E C P hC
  obtain ⟨q, hqP⟩ := hPoint
  have hEval : FE.eval₂ (algebraMap E E) (C 0) = 0 := by
    apply matchingProjectorLineIdeal_le_firstBasisCoordinateKernel C
    rw [hC]
    exact hFE
  have hOriginalEval : F.eval₂ (algebraMap k E) (C 0) = 0 := by
    simpa only [FE, MvPolynomial.eval₂_map, Algebra.algebraMap_self, RingHom.id_comp] using hEval
  have hqCubic : (q ≫ c) ≫ hypersurfaceToBase FE (hF.map (algebraMap k E)) = 𝟙 _ := by
    change (q ≫ schemeQuotientMap (equationIdeal FE (hF.map (algebraMap k E)))
      (projectorLineIdeal P) hContain) ≫ toBase (equationIdeal FE (hF.map (algebraMap k E))) = _
    rw [Category.assoc, schemeQuotientMap_toBase]
    exact hqP
  obtain ⟨y, hy, hFy⟩ := AllCharacteristics.homogeneous_cubic_degree_le_two_descent
    F hF (by omega : finrank k E ≤ 2) (C 0) (C.linearIndependent.ne_zero 0) hOriginalEval
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) F hF y hy hFy
  refine ⟨C, hC, e, heBase, c, hc, ?_, q, hqP, hqCubic, s, ?_⟩
  · exact schemeQuotientMap_comp_quotientProjMap _ _ _
  · simpa using hs

end PfaffianDescent.QuarticNet
