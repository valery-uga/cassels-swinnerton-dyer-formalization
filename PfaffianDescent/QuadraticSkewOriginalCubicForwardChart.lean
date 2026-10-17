import PfaffianDescent.QuadraticSkewOriginalCubicInverseChart
import PfaffianDescent.QuadraticSkewHomogeneousChartUnitEvaluation
import Mathlib.RingTheory.Localization.Away.Basic
/-! SOURCE ONLY / UNVERIFIED. Construct the actual forward scheme morphism
from coordinate solutions over a ring with unit quadratic denominator to the
quadratic basic open of the SAME original cubic. Its first inverse composite
is derived from polynomial coordinate identities, not a scheme-map premise. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.ForwardChart004
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open InverseChart
open scoped AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

private theorem cubicEvaluation_vanishes_on_ideal
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0) :
    ∀ p ∈ (equationIdeal F hF).toIdeal, p.eval₂ (algebraMap k A) x = 0 := by
  have hker : (equationIdeal F hF).toIdeal ≤
      RingHom.ker (eval₂Hom (algebraMap k A) x) := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact hFx
  exact fun p hp => hker hp

/-- Evaluation on the literal coordinate quotient of the original cubic. -/
def cubicCoordinateEvaluation
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0) :
    CoordinateRing (equationIdeal F hF) →+* A :=
  Ideal.Quotient.lift (equationIdeal F hF).toIdeal
    (eval₂Hom (algebraMap k A) x) (cubicEvaluation_vanishes_on_ideal F hF x hFx)

theorem cubicCoordinateEvaluation_mk
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (p : MvPolynomial (Fin 4) k) :
    cubicCoordinateEvaluation F hF x hFx
      (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) =
      p.eval₂ (algebraMap k A) x :=
  Ideal.Quotient.lift_mk _ _ _

/-- Actual Q-chart ring evaluation, valid without a unit linear coordinate. -/
def forwardChartRingHom
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x)) :
    QuadraticChartRing (equationIdeal F hF) Q →+* A :=
  UnitChart004.liftUnit (grading (equationIdeal F hF))
    (quadraticClass (equationIdeal F hF) Q)
    (cubicCoordinateEvaluation F hF x hFx) (by
      rw [quadraticClass, cubicCoordinateEvaluation_mk]
      exact hQunit)

theorem forwardChartRingHom_base
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x)) :
    (forwardChartRingHom F hF x hFx Q hQunit).comp
      (quadraticChartBaseMap (equationIdeal F hF) Q) = algebraMap k A := by
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply]
  change UnitChart004.liftUnit _ _ _ _
    (GradedChart.baseMap (grading (equationIdeal F hF))
      (z := quadraticClass (equationIdeal F hF) Q) a) = _
  rw [UnitChart004.liftUnit_baseMap]
  change cubicCoordinateEvaluation F hF x hFx
    (Ideal.Quotient.mk (equationIdeal F hF).toIdeal (C a)) = _
  rw [cubicCoordinateEvaluation_mk, MvPolynomial.eval₂_C]

theorem forwardChartRingHom_fraction_mul
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q R : MvPolynomial (Fin 4) k)
    (hQ : Q.IsHomogeneous 2) (hR : R.IsHomogeneous 2)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x)) :
    forwardChartRingHom F hF x hFx Q hQunit
      (quadraticFraction (equationIdeal F hF) Q R hQ hR) *
        Q.eval₂ (algebraMap k A) x = R.eval₂ (algebraMap k A) x := by
  have h := UnitChart004.liftUnit_mk_mul
    (grading (equationIdeal F hF)) (quadraticClass (equationIdeal F hF) Q)
    (cubicCoordinateEvaluation F hF x hFx)
    (by rw [quadraticClass, cubicCoordinateEvaluation_mk]; exact hQunit)
    (quadraticClass_mem (equationIdeal F hF) Q hQ) 1
    (quadraticClass (equationIdeal F hF) R)
    (by simpa only [one_smul] using quadraticClass_mem (equationIdeal F hF) R hR)
  change forwardChartRingHom F hF x hFx Q hQunit
    (quadraticFraction (equationIdeal F hF) Q R hQ hR) *
      (cubicCoordinateEvaluation F hF x hFx
        (quadraticClass (equationIdeal F hF) Q)) ^ 1 =
      cubicCoordinateEvaluation F hF x hFx
        (quadraticClass (equationIdeal F hF) R) at h
  simpa only [pow_one, quadraticClass, cubicCoordinateEvaluation_mk] using h

/-- The forward map lands in the actual quadratic basic OPEN scheme of the
original cubic, through its canonical homogeneous-localization isomorphism. -/
def originalCubicForwardHom
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x)) :
    Spec (.of A) ⟶ (Proj.basicOpen (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q)).toScheme :=
  Spec.map (CommRingCat.ofHom (forwardChartRingHom F hF x hFx Q hQunit)) ≫
    (Proj.basicOpenIsoSpec (grading (equationIdeal F hF))
      (quadraticClass (equationIdeal F hF) Q)
      (quadraticClass_mem (equationIdeal F hF) Q hQ) (by decide : 0 < 2)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalCubicForwardHom_over
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x)) :
    originalCubicForwardHom F hF x hFx Q hQ hQunit ≫
      (Proj.basicOpen (grading (equationIdeal F hF))
        (quadraticClass (equationIdeal F hF) Q)).ι ≫ hypersurfaceToBase F hF =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  have hι :
      (Proj.basicOpenIsoSpec (grading (equationIdeal F hF))
        (quadraticClass (equationIdeal F hF) Q)
        (quadraticClass_mem (equationIdeal F hF) Q hQ) (by decide : 0 < 2)).inv ≫
        (Proj.basicOpen (grading (equationIdeal F hF))
          (quadraticClass (equationIdeal F hF) Q)).ι =
      quadraticChartι (equationIdeal F hF) Q hQ := rfl
  dsimp only [hypersurfaceToBase]
  rw [originalCubicForwardHom, Category.assoc, ← Category.assoc _ _
    (toBase (equationIdeal F hF)), hι, quadraticChartι_toBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, forwardChartRingHom_base]

/-- Polynomial inverse identities give the first actual inverse composite. -/
theorem originalCubicForwardHom_inverse
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x))
    (R : PlaneIndex → MvPolynomial (Fin 4) k)
    (hR : ∀ i, (R i).IsHomogeneous 2) (t : PlaneIndex → A)
    (hRatios : ∀ i, (R i).eval₂ (algebraMap k A) x =
      t i * Q.eval₂ (algebraMap k A) x) :
    originalCubicForwardHom F hF x hFx Q hQ hQunit ≫
      originalCubicInverseHom F hF Q hQ R hR =
      Spec.map (CommRingCat.ofHom (eval₂Hom (algebraMap k A) t)) ≫
        (AffineSpace.SpecIso PlaneIndex (.of k)).inv := by
  have hcomp : (forwardChartRingHom F hF x hFx Q hQunit).comp
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR) =
      eval₂Hom (algebraMap k A) t := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, inverseCoordinateRingHom,
        MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun (forwardChartRingHom_base F hF x hFx Q hQunit) a
    · intro i
      rw [RingHom.comp_apply, inverseCoordinateRingHom_X, MvPolynomial.eval₂Hom_X']
      apply hQunit.mul_left_inj.mp
      exact (forwardChartRingHom_fraction_mul F hF x hFx Q (R i) hQ (hR i) hQunit).trans
        (hRatios i)
  unfold originalCubicForwardHom originalCubicInverseHom inverseChartSpecHom
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((forwardChartRingHom F hF x hFx Q hQunit).comp
      (inverseCoordinateRingHom (equationIdeal F hF) Q hQ R hR))) ≫ _ = _
  rw [hcomp]

end PfaffianDescent.QuadraticSkewRationality.ForwardChart004
