import PfaffianDescent.QuadraticSkewOriginalCubicChartEvaluationNaturality
/-! SOURCE ONLY / UNVERIFIED. An injective evaluation of the ORIGINAL
coordinate quotient supplies its canonical original coordinate vector and
the literal quadratic homogeneous chart inclusion. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)

def originalQuotientCoordinates
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) : Fin 4 → L :=
  fun i => e (Ideal.Quotient.mk (equationIdeal F hF).toIdeal (X i))

theorem originalQuotientEvaluation_comp_mk
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) :
    e.toRingHom.comp (Ideal.Quotient.mk (equationIdeal F hF).toIdeal) =
      eval₂Hom (algebraMap k L) (originalQuotientCoordinates F hF e) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    change e (algebraMap k (CoordinateRing (equationIdeal F hF)) a) = algebraMap k L a
    exact e.commutes a
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
    rfl

theorem originalQuotientCoordinates_on_equation
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) :
    F.eval₂ (algebraMap k L) (originalQuotientCoordinates F hF e) = 0 := by
  have hFzero : Ideal.Quotient.mk (equationIdeal F hF).toIdeal F = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton F)
  change (eval₂Hom (algebraMap k L) (originalQuotientCoordinates F hF e)) F = 0
  have h := RingHom.congr_fun (originalQuotientEvaluation_comp_mk F hF e) F
  simpa only [RingHom.comp_apply, hFzero, map_zero] using h.symm

theorem originalQuotientEvaluation_eq_coordinateEvaluation
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) :
    e.toRingHom = cubicCoordinateEvaluation F hF (originalQuotientCoordinates F hF e)
      (originalQuotientCoordinates_on_equation F hF e) := by
  apply Ideal.Quotient.ringHom_ext
  rw [originalQuotientEvaluation_comp_mk]
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, cubicCoordinateEvaluation_mk]
  rfl

theorem originalQuotient_quadratic_value
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) (Q : MvPolynomial (Fin 4) k) :
    e (quadraticClass (equationIdeal F hF) Q) =
      Q.eval₂ (algebraMap k L) (originalQuotientCoordinates F hF e) :=
  RingHom.congr_fun (originalQuotientEvaluation_comp_mk F hF e) Q

theorem originalQuotient_chart_evaluation
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) (Q : MvPolynomial (Fin 4) k)
    (hQunit : IsUnit (e (quadraticClass (equationIdeal F hF) Q))) :
    UnitChart004.liftUnit (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q) e.toRingHom hQunit =
    forwardChartRingHom F hF (originalQuotientCoordinates F hF e)
      (originalQuotientCoordinates_on_equation F hF e) Q
      (by rwa [← originalQuotient_quadratic_value F hF e Q]) := by
  unfold forwardChartRingHom
  simp only [← originalQuotientEvaluation_eq_coordinateEvaluation F hF e]

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
