import AllCharacteristics.ProjectivePoints
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Rational points on cubic surfaces over finite fields

Chevalley--Warning gives a nonzero zero of every homogeneous cubic in four
variables over a finite field.  The projective-coordinate construction then
turns it into a scheme-theoretic rational point.
-/

open AlgebraicGeometry CategoryTheory
open MvPolynomial

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- A homogeneous cubic in four variables over a finite field has a nonzero
zero in its ground field. -/
theorem finite_field_cubic_nonzero_solution
    {k : Type u} [Field k] [Finite k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ F.eval x = 0 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : DecidableEq k := Classical.decEq k
  have hdeg : F.totalDegree < Fintype.card (Fin 4) := by
    exact hF.totalDegree_le.trans_lt (by decide)
  have hdiv := char_dvd_card_solutions (ringChar k) hdeg
  by_contra h
  push Not at h
  have hzero : ∀ x : Fin 4 → k, F.eval x = 0 → x = 0 := by
    intro x hx
    by_contra hxzero
    exact h x hxzero hx
  have hFzero : F.eval (0 : Fin 4 → k) = 0 := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    exact hF.coeff_eq_zero (by simp)
  let x0 : {x : Fin 4 → k // F.eval x = 0} := ⟨0, hFzero⟩
  have hcard : Fintype.card {x : Fin 4 → k // F.eval x = 0} = 1 :=
    Fintype.card_eq_one_of_forall_eq (i := x0) (fun x => by
      apply Subtype.ext
      change (x : Fin 4 → k) = 0
      exact hzero x x.property)
  have hpone : ringChar k = 1 := Nat.dvd_one.mp (hcard ▸ hdiv)
  exact CharP.ringChar_ne_one hpone

/-- A homogeneous cubic in four variables over a finite field has a rational
section of its projective hypersurface. -/
theorem finite_field_cubic_has_rational_section
    {k : Type u} [Field k] [Finite k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨x, hx, hFx⟩ := finite_field_cubic_nonzero_solution F hF
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id k) F hF x hx
    (by simpa using hFx)
  exact ⟨s, by simpa using hs⟩

end HomogeneousProjective
end AllCharacteristics
