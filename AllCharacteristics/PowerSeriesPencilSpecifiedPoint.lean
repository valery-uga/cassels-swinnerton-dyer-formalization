import AllCharacteristics.SmoothLocusSpecifiedCompleteAlgebra
import AllCharacteristics.CubicPencil
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! SOURCE ONLY / UNVERIFIED. Exact L[[t]] lift for a GIVEN point on the
actual pencil's special fiber, known to lie in its relative smooth locus.
The separate original-surface interface has an explicitly documented pointwise
smoothness-transfer obligation; this theorem does not silently choose a point. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
attribute [local instance] MvPolynomial.gradedAlgebra

def prescribedPowerSeriesPencil (p g : MvPolynomial (Fin 4) k) :
    MvPolynomial (Fin 4) (PowerSeries k) :=
  (cubicPencil p g).map Polynomial.coeToPowerSeries.ringHom

theorem prescribedPowerSeriesPencil_homogeneous
    {p g : MvPolynomial (Fin 4) k}
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) :
    (prescribedPowerSeriesPencil p g).IsHomogeneous 3 :=
  (cubicPencil_isHomogeneous hp hg).map Polynomial.coeToPowerSeries.ringHom

theorem prescribedPowerSeriesPencil_constantCoeff (p g : MvPolynomial (Fin 4) k) :
    (prescribedPowerSeriesPencil p g).map PowerSeries.constantCoeff = p := by
  have hba : (PowerSeries.constantCoeff (R := k)).comp
      Polynomial.coeToPowerSeries.ringHom = Polynomial.evalRingHom 0 := by
    ext r
    change PowerSeries.constantCoeff (r : PowerSeries k) = r.eval 0
    exact Polynomial.coeff_zero_eq_eval_zero r
  change ((cubicPencil p g).map Polynomial.coeToPowerSeries.ringHom).map
    PowerSeries.constantCoeff = p
  rw [MvPolynomial.map_map, hba, cubicPencil_map_eval_zero]

theorem powerSeriesExtension_constantCoeff_square :
    (PowerSeries.constantCoeff (R := L)).comp
        (algebraMap (PowerSeries k) (PowerSeries L)) =
      (algebraMap k L).comp (PowerSeries.constantCoeff (R := k)) := by
  ext r
  change PowerSeries.constantCoeff (PowerSeries.map (algebraMap k L) r) =
    algebraMap k L (PowerSeries.constantCoeff r)
  rfl

/-- The actual GIVEN special point lifts over EXACTLY L[[t]], and its
reduction is EXACTLY that q. No unspecified finite coefficient algebra.
This intermediate theorem does not need finiteness of L/k at all. -/
theorem prescribedPowerSeriesPencil_lift_given_smooth_point
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg))
    (hq : q ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap k L).comp (PowerSeries.constantCoeff (R := k)))))
    (hsm : q (IsLocalRing.closedPoint L) ∈
      (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg)).smoothLocus) :
    ∃ s : Spec (.of (PowerSeries L)) ⟶ hypersurface
        (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg),
      s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L))) ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := L))) ≫ s = q := by
  letI : IsAdicComplete (maximalIdeal (PowerSeries L)) (PowerSeries L) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hq' : q ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom
        ((PowerSeries.constantCoeff (R := L)).comp
          (algebraMap (PowerSeries k) (PowerSeries L)))) := by
    rw [powerSeriesExtension_constantCoeff_square]
    exact hq
  exact lift_smoothLocus_point_to_specified_complete_local_algebra
    (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg))
    PowerSeries.constantCoeff PowerSeries.constantCoeff_surj q hq' hsm

end AllCharacteristics
