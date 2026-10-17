import PfaffianDescent.VoisinUniversalFourLineChange
import AllCharacteristics.KollarGenericResidual

/-!
# A transverse line on a fixed smooth cubic

The cubic is normalized at the first coordinate point.  Its equation in the
distinguished coordinate is irreducible over the generic-direction fraction
field, hence separable in characteristic zero.  Avoiding its discriminant,
the secant coefficient, and the cubic value of the direction produces one
actual line whose full cubic restriction is separable.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial AlgebraicGeometry
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

theorem cubicLinePolynomial_natDegree_eq_two_of_base_zero
    {K : Type u} [Field K] (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0) :
    (AllCharacteristics.cubicLinePolynomial c p d).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : 1 ≠ m := by omega
    have hm2 : m ≠ 2 := by omega
    simp [AllCharacteristics.cubicLinePolynomial, hp,
      Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, hm0, hm1, hm2]
  · simpa [AllCharacteristics.cubicLinePolynomial,
      Polynomial.coeff_C_mul] using hsec

/-- Reversing the orientation of a line through a cubic point adds the
known root at zero.  Its cubic discriminant is the square of the secant
coefficient times the discriminant of the residual quadratic orientation. -/
theorem cubicLinePolynomial_reversed_discr
    {K : Type u} [Field K] (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hdir : c.eval d ≠ 0) :
    (AllCharacteristics.cubicLinePolynomial c d p).discr =
      (c.mixed p d) ^ 2 *
        (AllCharacteristics.cubicLinePolynomial c p d).discr := by
  have htwo : (AllCharacteristics.cubicLinePolynomial c p d).degree = 2 := by
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 2)).mpr
    exact cubicLinePolynomial_natDegree_eq_two_of_base_zero c p d hp hsec
  have hthree : (AllCharacteristics.cubicLinePolynomial c d p).degree = 3 := by
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree c d p hdir
  rw [Polynomial.discr_of_degree_eq_three hthree,
    Polynomial.discr_of_degree_eq_two htwo]
  simp [AllCharacteristics.cubicLinePolynomial, hp,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  ring

/-- A normalized irreducible smooth cubic admits one affine line with a
degree-three separable restriction. -/
theorem exists_separable_cubic_line_of_normalized_irreducible
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (hirrF : Irreducible F)
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable := by
  let P := kollarDistinguishedCoordinatePolynomial c
  have hirr : Irreducible c.toMvPolynomial := by simpa [hc] using hirrF
  have hhom : c.toMvPolynomial.IsHomogeneous 3 := by simpa [hc] using hF
  have hdisc : P.discr ≠ 0 :=
    kollarDistinguishedCoordinatePolynomial_discr_ne_zero
      c hhom hirr hpoint hsec
  have hvalue : kollarDirectionCubicValuePolynomial c ≠ 0 :=
    kollarDirectionCubicValuePolynomial_ne_zero_of_irreducible
      F hF c hc hirrF
  have hsecPoly : kollarDirectionSecantPolynomial c ≠ 0 :=
    kollarDirectionSecantPolynomial_ne_zero c hsec
  let bad : Fin 3 → MvPolynomial (Fin 3) K :=
    ![P.discr, kollarDirectionCubicValuePolynomial c,
      kollarDirectionSecantPolynomial c]
  have hbad : ∀ i, bad i ≠ 0 := by
    intro i
    fin_cases i
    · exact hdisc
    · exact hvalue
    · exact hsecPoly
  obtain ⟨x, hx⟩ :=
    exists_mvPolynomial_eval_ne_zero_forall_of_finite bad hbad
  let d := kollarSpecializedProjectiveLineDirection K x
  let p := kollarBasePoint K
  have hdir : c.eval d ≠ 0 := by
    rw [← kollarDirectionCubicValuePolynomial_eval]
    exact hx 1
  have hsecx : c.mixed p d ≠ 0 := by
    rw [← kollarDirectionSecantPolynomial_eval]
    exact hx 2
  let g := kollarSpecializedDirectionPolynomial c x
  have hgEq : g = AllCharacteristics.cubicLinePolynomial c p d :=
    kollarSpecializedDirectionPolynomial_eq_cubicLinePolynomial c x
  have hPdegree : P.degree = 2 := by
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 2)).mpr
    exact kollarDistinguishedCoordinatePolynomial_natDegree_eq_two
      c hhom hpoint hsec
  have hgDegree : g.degree = 2 := by
    rw [hgEq]
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 2)).mpr
    exact cubicLinePolynomial_natDegree_eq_two_of_base_zero
      c p d hpoint hsecx
  have hgDisc : g.discr ≠ 0 := by
    have hmap := quadratic_discr_map_of_degree_two
      (MvPolynomial.eval₂Hom (RingHom.id K) x) P hPdegree hgDegree
    change g.discr = MvPolynomial.eval x P.discr at hmap
    rw [hmap]
    exact hx 0
  have hreverseDisc :
      (AllCharacteristics.cubicLinePolynomial c d p).discr ≠ 0 := by
    rw [cubicLinePolynomial_reversed_discr c p d hpoint hsecx hdir]
    exact mul_ne_zero (pow_ne_zero 2 hsecx) (by simpa [hgEq] using hgDisc)
  refine ⟨d, p, hdir, ?_⟩
  have hdegree :
      (AllCharacteristics.cubicLinePolynomial c d p).degree = 3 := by
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 3)).mpr
    exact AllCharacteristics.cubicLinePolynomial_natDegree c d p hdir
  exact polynomial_separable_of_discr_ne_zero _
    (by rw [hdegree]; decide) hreverseDisc

theorem exists_separable_cubic_line_of_normalized_smooth
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)]
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable := by
  have hc0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hF0 : F ≠ 0 := by simpa [hc] using hc0
  have hirrF : Irreducible F :=
    irreducible_of_smooth_homogeneous_cubic_of_field F hF hF0
  exact exists_separable_cubic_line_of_normalized_irreducible
    F hF c hc hirrF hpoint hsec

end PfaffianDescent
