import PfaffianDescent.QuadraticSkewOriginalQuotientFieldEvaluation
import PfaffianDescent.QuadraticSkewOriginalResidualFirstRingIdentity
/-! SOURCE ONLY / UNVERIFIED. Canonical evaluation of the original
homogeneous chart evaluates its inverse numerators to the literal original
fractions R_i(w)/Q(w), on the whole affine-plane polynomial algebra. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L : Type u} [Field k] [Field L] [Algebra k L]

theorem originalQuotient_chart_base
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L)
    (Q : MvPolynomial (Fin 4) k)
    (hQunit : IsUnit (e (quadraticClass (equationIdeal F hF) Q))) :
    (UnitChart004.liftUnit (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q) e.toRingHom hQunit).comp
        (quadraticChartBaseMap (equationIdeal F hF) Q) = algebraMap k L := by
  apply RingHom.ext
  intro a
  change UnitChart004.liftUnit (grading (equationIdeal F hF))
    (quadraticClass (equationIdeal F hF) Q) e.toRingHom hQunit
    (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal F hF))
      (z := quadraticClass (equationIdeal F hF) Q) a) = _
  rw [UnitChart004.liftUnit_baseMap]
  exact e.commutes a

theorem originalQuotient_chart_inverse_values
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQunit : IsUnit (e (quadraticClass (equationIdeal F hF) Q)))
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2) :
    (UnitChart004.liftUnit (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q) e.toRingHom hQunit).comp
        (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR) =
      eval₂Hom (algebraMap k L) (fun i =>
        (R i).eval₂ (algebraMap k L) (originalQuotientCoordinates F hF e) /
          Q.eval₂ (algebraMap k L) (originalQuotientCoordinates F hF e)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, inverseCoordinateRingHom, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (originalQuotient_chart_base F hF e Q hQunit) a
  · intro i
    rw [RingHom.comp_apply, inverseCoordinateRingHom_X, MvPolynomial.eval₂Hom_X']
    rw [originalQuotient_chart_evaluation]
    have hQw : IsUnit (Q.eval₂ (algebraMap k L) (originalQuotientCoordinates F hF e)) := by
      rwa [← originalQuotient_quadratic_value F hF e Q]
    apply (eq_div_iff hQw.ne_zero).mpr
    exact forwardChartRingHom_fraction_mul F hF _ _ Q (R i) hQ (hR i) hQw

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
