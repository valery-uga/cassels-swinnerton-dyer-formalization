import PfaffianDescent.CoraySmoothNormalizedCurveBridge
import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.PolynomialCoordinateOne

/-! Actual projective two-equation charts, with constructed elimination maps.
STATUS: UNVERIFIED source only. No compiler has been run by the worker.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal homogeneous intersection ideal, with both original equations. -/
def projectiveIntersectionIdeal (p q : MvPolynomial (Fin 4) K)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) :=
  equationIdeal p hp ⊔ equationIdeal q hq

/-- Its underlying ideal is the literal two-generator ideal. -/
theorem projectiveIntersectionIdeal_toIdeal (p q : MvPolynomial (Fin 4) K)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) :
    (projectiveIntersectionIdeal p q hp hq).toIdeal = Ideal.span {p, q} := by
  rw [projectiveIntersectionIdeal, HomogeneousIdeal.toIdeal_sup]
  change Ideal.span {p} ⊔ Ideal.span {q} = Ideal.span {p, q}
  exact (Ideal.span_insert p ({q} : Set (MvPolynomial (Fin 4) K))).symm

/-- Eliminating the distinguished coordinate commutes with BOTH equations. -/
def coordinateOnePairQuotientEquiv (p q : MvPolynomial (Fin 4) K) (j : Fin 4) :
    (MvPolynomial (Fin 4) K ⧸ (Ideal.span {p, q} ⊔ coordinateOneIdeal j)) ≃+*
      (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
        Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q}) := by
  let I : Ideal (MvPolynomial (Fin 4) K) := coordinateOneIdeal j
  let J : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {p, q}
  let E := coordinateOneQuotientEquiv (R := K) j
  have hJ : Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q} =
      (J.map (Ideal.Quotient.mk I)).map E.toRingHom := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    change Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q} =
      Ideal.span {E (Ideal.Quotient.mk I p), E (Ideal.Quotient.mk I q)}
    have hpE : E (Ideal.Quotient.mk I p) = coordinateOneEvaluation j p :=
      coordinateOneQuotientEquiv_mk j p
    have hqE : E (Ideal.Quotient.mk I q) = coordinateOneEvaluation j q :=
      coordinateOneQuotientEquiv_mk j q
    rw [hpE, hqE]
  exact (Ideal.quotEquivOfEq (sup_comm J I)).trans
    ((DoubleQuot.quotQuotEquivQuotSup I J).symm.trans
      (Ideal.quotientEquiv (J.map (Ideal.Quotient.mk I))
        (Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q})
        E.toRingEquiv hJ))

/-- The actual projective chart is the literal Fin3 affine pair quotient.
Both elimination and retained-variable renaming are constructed. -/
def projectiveIntersection_chartRingEquiv (p q : MvPolynomial (Fin 4) K)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (j : Fin 4) :
    ChartRing (projectiveIntersectionIdeal p q hp hq) j ≃+*
      affineCurveRing (normalizedAffineEquation j p) (normalizedAffineEquation j q) := by
  let E := (MvPolynomial.renameEquiv K (finSuccAboveEquiv j)).symm
  let J : Ideal (MvPolynomial {i : Fin 4 // i ≠ j} K) :=
    Ideal.span {coordinateOneEvaluation j p, coordinateOneEvaluation j q}
  have hp' : E (coordinateOneEvaluation j p) = normalizedAffineEquation j p := by
    simpa only [E, AlgEquiv.symm_apply_apply] using
      (congrArg E (normalizedAffineEquation_rename_retained j p)).symm
  have hq' : E (coordinateOneEvaluation j q) = normalizedAffineEquation j q := by
    simpa only [E, AlgEquiv.symm_apply_apply] using
      (congrArg E (normalizedAffineEquation_rename_retained j q)).symm
  have hJ : affineCurveIdeal (normalizedAffineEquation j p) (normalizedAffineEquation j q) =
      J.map E.toRingHom := by
    simp only [affineCurveIdeal, J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    change Ideal.span {normalizedAffineEquation j p, normalizedAffineEquation j q} =
      Ideal.span {E (coordinateOneEvaluation j p), E (coordinateOneEvaluation j q)}
    rw [hp', hq']
  have eC : ChartRing (projectiveIntersectionIdeal p q hp hq) j ≃+*
      (MvPolynomial (Fin 4) K ⧸ (Ideal.span {p, q} ⊔ coordinateOneIdeal j)) := by
    have hrelations : chartPresentationIdeal (projectiveIntersectionIdeal p q hp hq) j =
        Ideal.span {p, q} ⊔ coordinateOneIdeal j := by
      change (projectiveIntersectionIdeal p q hp hq).toIdeal ⊔ coordinateOneIdeal j = _
      rw [projectiveIntersectionIdeal_toIdeal]
    exact (chartPresentationEquiv (projectiveIntersectionIdeal p q hp hq) j).symm.trans
      (Ideal.quotEquivOfEq hrelations)
  exact eC.trans ((coordinateOnePairQuotientEquiv p q j).trans
    (Ideal.quotientEquiv J
      (affineCurveIdeal (normalizedAffineEquation j p) (normalizedAffineEquation j q))
      E.toRingEquiv hJ))

/-- Actual smooth cubic and literal nonmembership give dimension at most one
in EVERY actual projective intersection coordinate chart. No integral-branch
hypothesis is needed for this dimension statement. -/
theorem projectiveIntersection_chart_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (j : Fin 4) :
    ringKrullDim (ChartRing (projectiveIntersectionIdeal p q hp hq) j) ≤ 1 := by
  rw [ringKrullDim_eq_of_ringEquiv (projectiveIntersection_chartRingEquiv p q hp hq j)]
  exact normalizedProjectiveCurve_ringKrullDim_le_one p q hp hp0 n hq hnot j

end PfaffianDescent.Coray
