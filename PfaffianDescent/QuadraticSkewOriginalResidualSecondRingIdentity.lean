import PfaffianDescent.QuadraticSkewOriginalInverseFieldReconstruction
import PfaffianDescent.QuadraticSkewOriginalChartInverseFieldEvaluation
/-! SOURCE ONLY / UNVERIFIED. Derive the SECOND actual inverse identity
on the original inverse-domain ring. The whole-chart identity is proved
from the original ambient-coordinate reconstruction in an injective field
evaluation. No scheme-map identity, dense-open isomorphism, BirationalOver,
or IsRationalOver certificate is an input. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial AlgebraicGeometry Module QuarticNet OriginalBridge AmbientResidual
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k E L : Type u} [Field k] [Field E] [Field L]
variable [Algebra k E] [Algebra k L]

def originalInverseNumerators
    (R_T R_U : MvPolynomial (Fin 4) k) : PlaneIndex → MvPolynomial (Fin 4) k :=
  fun i => ![R_T, R_U] i.down

theorem originalInverseNumerators_homogeneous
    (R_T R_U : MvPolynomial (Fin 4) k)
    (hT : R_T.IsHomogeneous 2) (hU : R_U.IsHomogeneous 2) :
    ∀ i, (originalInverseNumerators R_T R_U i).IsHomogeneous 2 := by
  rintro ⟨i⟩
  fin_cases i
  · exact hT
  · exact hU

theorem original_residual_second_ring_identity
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (e : CoordinateRing (equationIdeal F hF) →ₐ[k] L) (heinj : Function.Injective e)
    (f : E →ₐ[k] L) (C : Basis (Fin 4) E (Fin 4 → E))
    (α β δ : E) (hαβ : α ≠ β) (hδ : δ ≠ 0)
    (hLeft : linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F) ∈
      Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F) ∈
      Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)))
    (r : Fin 4 → PlanePolynomial k)
    (hr : ∀ i, MvPolynomial.map (algebraMap k E) (r i) = MvPolynomial.C δ *
      originalAmbientResidual C α β
        (linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)) i)
    (Q R_T R_U : MvPolynomial (Fin 4) k)
    (hQ : Q.IsHomogeneous 2) (hT : R_T.IsHomogeneous 2) (hU : R_U.IsHomogeneous 2)
    (hQmap : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (hTmap : MvPolynomial.map (algebraMap k E) R_T = MvPolynomial.C (α - β)⁻¹ *
      (MvPolynomial.C α * pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0 -
        MvPolynomial.C β * pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2))
    (hUmap : MvPolynomial.map (algebraMap k E) R_U = MvPolynomial.C (α - β)⁻¹ *
      (pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2 -
        pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0))
    (N : PlanePolynomial k) (hN : N ≠ 0)
    (hFr : F.eval₂ (algebraMap k (PlanePolynomial k)) r = 0)
    (a : k) (ha : a ≠ 0)
    (hQeval : Q.eval₂ (algebraMap k (PlanePolynomial k)) r = MvPolynomial.C a * N)
    (hRatios : ∀ i, (originalInverseNumerators R_T R_U i).eval₂
      (algebraMap k (PlanePolynomial k)) r =
        X i * Q.eval₂ (algebraMap k (PlanePolynomial k)) r) :
    let R := originalInverseNumerators R_T R_U
    let hR := originalInverseNumerators_homogeneous R_T R_U hT hU
    let θ := inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR
    let φ := forwardChartRingHom F hF (localizedResidualCoordinates N r)
      (by rw [localizedResidualCoordinates_eval, hFr, map_zero]) Q
      (localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval)
    (inverseLocalizationHom (S := PlaneLocalization N)
      (T := Localization.Away (θ N)) N θ).comp φ =
        algebraMap (QuadraticChartRing (equationIdeal F hF) Q) (Localization.Away (θ N)) := by
  let R := originalInverseNumerators R_T R_U
  let hR := originalInverseNumerators_homogeneous R_T R_U hT hU
  let H := QuadraticChartRing (equationIdeal F hF) Q
  let θ := inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR
  let S := PlaneLocalization N
  let T := Localization.Away (θ N)
  let x := localizedResidualCoordinates N r
  have hFx : F.eval₂ (algebraMap k S) x = 0 := by
    rw [localizedResidualCoordinates_eval, hFr, map_zero]
  have hQx : IsUnit (Q.eval₂ (algebraMap k S) x) :=
    localizedResidualCoordinates_quadratic_isUnit N r Q a ha hQeval
  let φ := forwardChartRingHom F hF x hFx Q hQx
  have hfirst : φ.comp θ = algebraMap (PlanePolynomial k) S :=
    residual_forward_ring_comp_inverse F hF Q hQ N r hFr a ha hQeval R hR hRatios
  letI : IsDomain S := IsLocalization.Away.isDomain S hN
  have hQr : Q.eval₂ (algebraMap k (PlanePolynomial k)) r ≠ 0 := by
    rw [hQeval]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr ha) hN
  have hz : quadraticClass (equationIdeal F hF) Q ≠ 0 :=
    quadraticClass_ne_zero_of_residual F hF Q r hFr hQr
  have heQ : e (quadraticClass (equationIdeal F hF) Q) ≠ 0 := by
    intro h
    apply hz
    apply heinj
    simpa only [map_zero] using h
  let ψ : H →+* L := UnitChart004.liftUnit (grading (equationIdeal F hF))
    (quadraticClass (equationIdeal F hF) Q) e.toRingHom (isUnit_iff_ne_zero.mpr heQ)
  have hψinj : Function.Injective ψ := UnitChart005.liftUnit_injective _ _ _ _ heinj
  have hn : θ N ≠ 0 := by
    have hu : IsUnit (φ (θ N)) := by
      rw [← RingHom.comp_apply, hfirst]
      exact IsLocalization.Away.algebraMap_isUnit N
    intro h
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
  have hψn : ψ (θ N) ≠ 0 := by
    intro h
    apply hn
    apply hψinj
    simpa only [map_zero] using h
  let l : T →+* L := IsLocalization.Away.lift (θ N) (isUnit_iff_ne_zero.mpr hψn)
  have hlinj : Function.Injective l :=
    localizationLift_injective (T := T) N θ ψ hψinj (isUnit_iff_ne_zero.mpr hψn)
  let betaMap : S →+* T := inverseLocalizationHom N θ
  have hlβ (p : PlanePolynomial k) :
      l (betaMap (algebraMap (PlanePolynomial k) S p)) = ψ (θ p) := by
    rw [inverseLocalizationHom_base, IsLocalization.Away.lift_eq]
  let w := originalQuotientCoordinates F hF e
  have hFw : F.eval₂ (algebraMap k L) w = 0 := originalQuotientCoordinates_on_equation F hF e
  have hQw : IsUnit (Q.eval₂ (algebraMap k L) w) := by
    rw [← originalQuotient_quadratic_value F hF e Q]
    exact isUnit_iff_ne_zero.mpr heQ
  have hψcanonical : ψ = forwardChartRingHom F hF w hFw Q hQw :=
    originalQuotient_chart_evaluation F hF e Q (isUnit_iff_ne_zero.mpr heQ)
  have hθfield : ψ.comp θ = eval₂Hom (algebraMap k L)
      (originalInverseFieldParameters w Q R_T R_U) := by
    have ht := originalQuotient_chart_inverse_values F hF e Q hQ
      (isUnit_iff_ne_zero.mpr heQ) R hR
    have hparams : (fun i => (R i).eval₂ (algebraMap k L) w /
        Q.eval₂ (algebraMap k L) w) = originalInverseFieldParameters w Q R_T R_U := by
      ext i
      rcases i with ⟨i⟩
      fin_cases i <;> simp [R, originalInverseNumerators, originalInverseFieldParameters]
    exact ht.trans (congrArg (eval₂Hom (algebraMap k L)) hparams)
  have hfbase : (l.comp betaMap).comp (algebraMap k S) = algebraMap k L := by
    ext b
    rw [RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply k (PlanePolynomial k) S]
    change l (betaMap (algebraMap (PlanePolynomial k) S (MvPolynomial.C b))) = _
    rw [hlβ]
    exact (RingHom.congr_fun hθfield (MvPolynomial.C b)).trans
      (MvPolynomial.eval₂Hom_C (algebraMap k L)
        (originalInverseFieldParameters w Q R_T R_U) b)
  let y : Fin 4 → L := fun i => l (betaMap (x i))
  have hy : y = (fun i => (r i).eval₂ (algebraMap k L)
      (originalInverseFieldParameters w Q R_T R_U)) := by
    ext i
    change l (betaMap (algebraMap (PlanePolynomial k) S (r i))) = _
    rw [hlβ]
    exact RingHom.congr_fun hθfield (r i)
  have hEval (p : MvPolynomial (Fin 4) k) :
      p.eval₂ (algebraMap k L) y = (l.comp betaMap) (p.eval₂ (algebraMap k S) x) := by
    have h := (MvPolynomial.hom_eval₂ p (algebraMap k S) (l.comp betaMap) x).symm
    rw [hfbase] at h
    exact h
  have hFy : F.eval₂ (algebraMap k L) y = 0 :=
    (hEval F).trans ((congrArg (l.comp betaMap) hFx).trans (map_zero _))
  have hQy : IsUnit (Q.eval₂ (algebraMap k L) y) :=
    (hEval Q).symm ▸ hQx.map (l.comp betaMap)
  obtain ⟨c, hc, hrec⟩ := original_inverse_field_reconstructs_residual
    C f α β δ hαβ hδ F hF hLeft hRight r hr Q R_T R_U hQmap hTmap hUmap w hFw
      hQw.ne_zero (by rw [← hy]; exact hQy.ne_zero)
  have hfield : (l.comp betaMap).comp φ = ψ := by
    rw [hψcanonical]
    change (l.comp betaMap).comp (forwardChartRingHom F hF x hFx Q hQx) = _
    rw [forwardChartRingHom_comp F hF x hFx Q hQx (l.comp betaMap) hfbase hFy hQy]
    exact forwardChartRingHom_eq_of_unit_scale F hF w y hFw hFy Q hQ hQw hQy
      c (isUnit_iff_ne_zero.mpr hc) (hy.trans hrec)
  apply RingHom.ext
  intro b
  apply hlinj
  exact (RingHom.congr_fun hfield b).trans
    (IsLocalization.Away.lift_eq (θ N) (isUnit_iff_ne_zero.mpr hψn) b).symm

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
