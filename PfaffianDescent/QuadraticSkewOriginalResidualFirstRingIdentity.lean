import PfaffianDescent.QuadraticSkewChartLocalizationInverses
import PfaffianDescent.QuadraticSkewOriginalCubicForwardPrincipalPlane
/-! SOURCE ONLY / UNVERIFIED. The first polynomial inverse identity on
the whole original homogeneous chart is retained as a ring identity for
both actual ordinary localization lifts. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
variable {k : Type u} [Field k]

theorem residual_forward_ring_comp_inverse
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (N : PlanePolynomial k) (r : Fin 4 → PlanePolynomial k)
    (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
    (a : k) (ha : a ≠ 0)
    (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = C a * N)
    (R : PlaneIndex → MvPolynomial (Fin 4) k) (hR : ∀ i, (R i).IsHomogeneous 2)
    (hRatios : ∀ i, (R i).eval₂ (algebraMap k (PlanePolynomial k)) r =
      X i * Q.eval₂ (algebraMap k (PlanePolynomial k)) r) :
    (forwardChartRingHom F hF (localizedResidualCoordinates N r)
      (by rw [localizedResidualCoordinates_eval, hFr, map_zero]) Q
      (localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval)).comp
        (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR) =
      algebraMap (PlanePolynomial k) (PlaneLocalization N) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, inverseCoordinateRingHom, MvPolynomial.eval₂Hom_C]
    simpa only [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply k (PlanePolynomial k) (PlaneLocalization N),
      MvPolynomial.algebraMap_eq] using
      RingHom.congr_fun (forwardChartRingHom_base F hF _ _ Q
        (localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval)) b
  · intro i
    rw [RingHom.comp_apply, inverseCoordinateRingHom_X]
    have hunit := localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval
    apply hunit.mul_left_inj.mp
    rw [forwardChartRingHom_fraction_mul F hF _ _ Q (R i) hQ (hR i) hunit,
      localizedResidualCoordinates_eval, hRatios i, map_mul,
      localizedResidualCoordinates_eval]

theorem quadraticClass_ne_zero_of_residual
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (Q : MvPolynomial (Fin 4) k) (r : Fin 4 → PlanePolynomial k)
    (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
    (hQr : Q.eval₂ (algebraMap k (PlanePolynomial k)) r ≠ 0) :
    quadraticClass (equationIdeal F hF) Q ≠ 0 := by
  intro hz
  have h := cubicCoordinateEvaluation_mk F hF r hFr Q
  change cubicCoordinateEvaluation F hF r hFr
    (quadraticClass (equationIdeal F hF) Q) = _ at h
  rw [hz, map_zero] at h
  exact hQr h.symm

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
