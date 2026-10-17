import AllCharacteristics.CubicMultiplicity
import AllCharacteristics.CubicPolynomialCoordinates

/-!
# Reduction of a singular extension point on a cubic

Given a point over a finite extension of degree prime to three, the
multiplicity trichotomy either produces a smooth point over that same
extension or a rational point over the ground field.  The triple-point branch
uses directional-derivative descent outside characteristic three and the
trace of a normalized universal translation direction in characteristic
three.
-/

open scoped BigOperators
namespace AllCharacteristics
open PfaffianDescent

universe u

/-- A point of a homogeneous cubic over an extension of degree prime to three
either already descends to the ground field or can be replaced by a smooth
point over the same extension.  There is no characteristic, separability, or
smoothness hypothesis on the original cubic. -/
theorem cubic_point_or_smooth_extension_point
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (he : p.eval₂ (algebraMap k L) x = 0) :
    (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ∨
      ∃ q : Fin 4 → L,
        IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) q := by
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic
    (p.map (algebraMap k L)) (hp.map (algebraMap k L))
  have hce : c.eval x = 0 := by
    have h := he
    rw [MvPolynomial.eval₂_eq_eval_map, ← hc] at h
    change MvPolynomial.eval₂ (RingHom.id L) x c.toMvPolynomial = 0 at h
    rw [PfaffianDescent.Cubic.eval_toMvPolynomial] at h
    exact h
  by_cases hs : ∃ d : Fin 4 → L, c.mixed x d ≠ 0
  · obtain ⟨d, hd⟩ := hs
    right
    refine ⟨x, ?_⟩
    simpa only [hc] using
      Cubic.isSmoothCoordinatePoint_of_mixed_ne_zero c x d hx hce hd
  push Not at hs
  by_cases hd : ∃ a : Fin 4 → L, c.mixed a x ≠ 0
  · obtain ⟨a, ha⟩ := hd
    right
    obtain ⟨q, hq⟩ := Cubic.exists_smoothCoordinatePoint_of_double_mixed
      c x hce hs ha
    exact ⟨q, by simpa only [hc] using hq⟩
  push Not at hd
  have htransC : IsTranslationDirection c.toMvPolynomial x :=
    Cubic.isTranslationDirection_toMvPolynomial c x hce hd hs
  have htrans : IsTranslationDirection (p.map (algebraMap k L)) x := by
    rw [← hc]
    exact htransC
  by_cases hthree : (3 : k) = 0
  · letI : CharP k 3 :=
      (CharP.charP_iff_prime_eq_zero (by decide)).2 hthree
    have hcoordinate : ∃ i : Fin 4, x i ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hcoordinate
    let w : Fin 4 → L := (x i)⁻¹ • x
    have hwi : w i = 1 := by
      simp [w, hi]
    have hwtrans : IsTranslationDirection (p.map (algebraMap k L)) w := by
      exact htrans.smul (x i)⁻¹
    left
    exact exists_ground_cubic_point_of_translation_char_three
      p hp hdegree w i hwi hwtrans
  · have hmixed :
        (c.map MvPolynomial.C).mixed MvPolynomial.X
          (fun i ↦ MvPolynomial.C (x i)) = 0 :=
      Cubic.mixed_left_map_eq_zero c x hd MvPolynomial.C MvPolynomial.X
    have hdirL : directionalDerivative c.toMvPolynomial x = 0 := by
      simpa only [Cubic.mixed_polynomial_eq_directionalDerivative] using hmixed
    have hdir : ∑ i, MvPolynomial.C (x i) *
        (MvPolynomial.pderiv i p).map (algebraMap k L) = 0 := by
      simpa only [hc, directionalDerivative, MvPolynomial.pderiv_map] using hdirL
    left
    exact exists_ground_cubic_point_of_extension_direction
      p hp hthree x hx hdir

end AllCharacteristics
