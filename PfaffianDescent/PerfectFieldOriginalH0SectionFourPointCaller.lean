import PfaffianDescent.SingleSupportOriginalH0SectionFourPointCaller
import PfaffianDescent.PerfectFieldClosedQuarticOriginalTangentHZero
import PfaffianDescent.IndependentCoplanarQuarticPoint

/-! SOURCE ONLY. Actual rank-eight/H0 construction from the ORIGINAL point
feeds the same-original-Z tangent graph consumers. Coplanar points use only
the independent conic/complement/secant helper, never a degree-four endpoint. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_closedQuarticPoint_originalHZero_graph_rational_section
    {k : Type u} [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (P : closedPoints (hypersurface F hF))
    (h4 : (hypersurfaceToBase F hF).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal F hF)
      ((hypersurface F hF).fromSpecResidueField P.1)) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase F hF) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase F hF) P
  let L := (hypersurface F hF).residueField P.1
  letI : Module.Finite k (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  obtain ⟨q, hq, hbase, hSupport, hReduce, hfinite, hRank, hSplit, hdim⟩ :=
    perfectField_closedQuarticPoint_exists_original_tangentSubscheme_actualHZero
      F hF hF₀ P h4 hGeom
  let qOriginal : Spec (.of (DualNumber L)) ⟶ scheme (equationIdeal F hF) := q
  letI : IsClosedImmersion qOriginal := hq
  letI : IsFinite (qOriginal ≫ toBase (equationIdeal F hF)) := hfinite
  letI : IsClosedImmersion (qOriginal ≫ quotientProjMap (equationIdeal F hF)) := by
    infer_instance
  have hdim' : 3 ≤ finrank k
      (ActualP3IdealQuadraticHZero (qOriginal ≫ quotientProjMap (equationIdeal F hF))) := hdim
  exact singleSupport_originalZ_actual_H0_has_section
    F hF hF₀ qOriginal P hSupport h4 hGeom hdim' hRank

/-- Literal thm:4->1 hypotheses. All geometric spanning, rank8, genuine
H0 dimension, field/line data, full-base alternatives and residual data are
constructed in the proof from the original degree-four closed point. -/
theorem perfectField_degree_four_originalHZero_graph_rational_section
    {k : Type u} [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (P : closedPoints (hypersurface F hF))
    (h4 : (hypersurfaceToBase F hF).residueDegree P.1 = 4) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  by_cases hplane : ∃ c : Fin 4 → k, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal F hF).toIdeal (homogeneousLinearForm c) ∈
        P.1.asHomogeneousIdeal.toIdeal
  · obtain ⟨c, hc, hmem⟩ := hplane
    exact cubic_coplanar_degree_four_independent_conic_secant_descent F hF P h4 c hc hmem
  · have hGeom : ProjectiveGeometricGeneralPosition (equationIdeal F hF)
        ((hypersurface F hF).fromSpecResidueField P.1) :=
      perfectField_cubic_closedPoint_degree_four_general_position F hF P h4 hplane
    exact perfectField_closedQuarticPoint_originalHZero_graph_rational_section
      F hF hF₀ P h4 hGeom

end PfaffianDescent
