import PfaffianDescent.QuadraticSkewOriginalCubicForwardChart
import Mathlib.Tactic.Ring
/-! SOURCE ONLY / UNVERIFIED. Exact whole-chart reconstruction under a unit
scalar in an arbitrary commutative coordinate ring. This is the algebraic
second-composite machinery; no scheme identity or birationality is assumed. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.ForwardChart004
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective InverseChart
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

theorem forwardChartRingHom_mk_mul
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQunit : IsUnit (Q.eval₂ (algebraMap k A) x))
    (n : ℕ) (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous (n • 2)) :
    forwardChartRingHom F hF x hFx Q hQunit
      (Away.mk (grading (equationIdeal F hF))
        (quadraticClass_mem (equationIdeal F hF) Q hQ) n
        (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) ⟨p, hp, rfl⟩) *
      (Q.eval₂ (algebraMap k A) x) ^ n = p.eval₂ (algebraMap k A) x := by
  have h := UnitChart004.liftUnit_mk_mul
    (grading (equationIdeal F hF)) (quadraticClass (equationIdeal F hF) Q)
    (cubicCoordinateEvaluation F hF x hFx)
    (by rw [quadraticClass, cubicCoordinateEvaluation_mk]; exact hQunit)
    (quadraticClass_mem (equationIdeal F hF) Q hQ) n
    (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) ⟨p, hp, rfl⟩
  change forwardChartRingHom F hF x hFx Q hQunit
    (Away.mk (grading (equationIdeal F hF))
      (quadraticClass_mem (equationIdeal F hF) Q hQ) n
      (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) ⟨p, hp, rfl⟩) *
      (cubicCoordinateEvaluation F hF x hFx
        (quadraticClass (equationIdeal F hF) Q)) ^ n =
      cubicCoordinateEvaluation F hF x hFx
        (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) at h
  simpa only [quadraticClass, cubicCoordinateEvaluation_mk] using h

/-- Explicit coordinate reconstruction up to a unit scalar gives equality
on the entire actual original quadratic homogeneous chart, in every degree. -/
theorem forwardChartRingHom_eq_of_unit_scale
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x y : Fin 4 → A)
    (hFx : F.eval₂ (algebraMap k A) x = 0)
    (hFy : F.eval₂ (algebraMap k A) y = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQx : IsUnit (Q.eval₂ (algebraMap k A) x))
    (hQy : IsUnit (Q.eval₂ (algebraMap k A) y))
    (u : A) (hu : IsUnit u) (hscaled : y = u • x) :
    forwardChartRingHom F hF y hFy Q hQy =
      forwardChartRingHom F hF x hFx Q hQx := by
  apply RingHom.ext
  intro b
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading (equationIdeal F hF))
    (quadraticClass_mem (equationIdeal F hF) Q hQ) b
  obtain ⟨p, hp, rfl⟩ := ha
  have hx := forwardChartRingHom_mk_mul F hF x hFx Q hQ hQx n p hp
  have hy := forwardChartRingHom_mk_mul F hF y hFy Q hQ hQy n p hp
  have hpEval : p.eval₂ (algebraMap k A) y =
      u ^ (n • 2) * p.eval₂ (algebraMap k A) x := by
    rw [hscaled, eval₂_homogeneous_smul p hp]
  have hQEval : Q.eval₂ (algebraMap k A) y =
      u ^ 2 * Q.eval₂ (algebraMap k A) x := by
    rw [hscaled, eval₂_homogeneous_smul Q hQ]
  have hpow : (u ^ 2 * Q.eval₂ (algebraMap k A) x) ^ n =
      u ^ (n • 2) * (Q.eval₂ (algebraMap k A) x) ^ n := by
    rw [mul_pow, ← pow_mul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  apply (hQy.pow n).mul_left_inj.mp
  calc
    _ = p.eval₂ (algebraMap k A) y := hy
    _ = u ^ (n • 2) * p.eval₂ (algebraMap k A) x := hpEval
    _ = _ := by
      rw [hQEval, hpow, ← hx]
      let c := forwardChartRingHom F hF x hFx Q hQx
        (Away.mk (grading (equationIdeal F hF))
          (quadraticClass_mem (equationIdeal F hF) Q hQ) n
          (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) ⟨p, hp, rfl⟩)
      change u ^ (n • 2) * (c * (Q.eval₂ (algebraMap k A) x) ^ n) =
        c * (u ^ (n • 2) * (Q.eval₂ (algebraMap k A) x) ^ n)
      exact mul_left_comm _ _ _

/-- The coordinate-scaling proof gives equality of actual maps into the
same original basic open, ready for the recovered inverse composite. -/
theorem originalCubicForwardHom_eq_of_unit_scale
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x y : Fin 4 → A)
    (hFx : F.eval₂ (algebraMap k A) x = 0)
    (hFy : F.eval₂ (algebraMap k A) y = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQx : IsUnit (Q.eval₂ (algebraMap k A) x))
    (hQy : IsUnit (Q.eval₂ (algebraMap k A) y))
    (u : A) (hu : IsUnit u) (hscaled : y = u • x) :
    originalCubicForwardHom F hF y hFy Q hQ hQy =
      originalCubicForwardHom F hF x hFx Q hQ hQx := by
  unfold originalCubicForwardHom
  rw [forwardChartRingHom_eq_of_unit_scale F hF x y hFx hFy Q hQ hQx hQy u hu hscaled]

end PfaffianDescent.QuadraticSkewRationality.ForwardChart004
