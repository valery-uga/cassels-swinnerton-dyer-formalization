import PfaffianDescent.CorayBoundedOriginalSectionFamily
import PfaffianDescent.CorayGradedCoordinateMultiplication
import Mathlib.Data.Nat.Find

/-! SOURCE ONLY / UNVERIFIED. Choose the first nonzero actual quotient
grade through the original point, rather than assuming a minimal-degree
certificate. Lower grades are injective at the point. In the original
FIELD-valued case this rules out lower-grade products through the point.
This is not geometric irreducibility of the intersection on the cubic. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- The actual Hilbert window internally produces a first nonzero
through-point quotient grade. Every smaller actual evaluation is injective.
No image/rank/transversality premise is supplied. -/
theorem exists_least_cubicThroughPoint_degree [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (y : Fin 4 → A) (hpy : p.eval₂ (algebraMap K A) y = 0)
    (hsize : finrank K A + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    ∃ a ≤ n, ∃ s : cubicThroughCoordinateSections p hp a y hpy,
      s ≠ 0 ∧ ∀ b < a,
        Function.Injective (cubicGradeCoordinateEvaluation p hp b y hpy) := by
  classical
  have h5 := cubicThroughCoordinateSections_finrank_ge_five p hp hp0 n y hpy hsize
  letI : Nontrivial (cubicThroughCoordinateSections p hp n y hpy) :=
    Module.nontrivial_of_finrank_pos (R := K) (lt_of_lt_of_le (by decide) h5)
  obtain ⟨s, hs⟩ := exists_ne (0 : cubicThroughCoordinateSections p hp n y hpy)
  have hex : ∃ a : ℕ, ∃ s : cubicThroughCoordinateSections p hp a y hpy, s ≠ 0 :=
    ⟨n, s, hs⟩
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨s, hs⟩, t, ht, ?_⟩
  intro b hb r t hrt
  have hzero (v : grading (equationIdeal p hp) b)
      (hv : cubicGradeCoordinateEvaluation p hp b y hpy v = 0) : v = 0 := by
    by_contra hv0
    have hmem : v ∈ cubicThroughCoordinateSections p hp b y hpy := hv
    have hnonzero : (⟨v, hmem⟩ : cubicThroughCoordinateSections p hp b y hpy) ≠ 0 := by
      intro h
      exact hv0 (congrArg Subtype.val h)
    exact Nat.find_min hex hb ⟨⟨v, hmem⟩, hnonzero⟩
  exact sub_eq_zero.mp (hzero (r - t) (by rw [map_sub, hrt, sub_self]))

/-- In a genuinely minimal degree, lower-degree homogeneous polynomials
through the point are exactly cubic relations. The conclusion is in the
original K polynomial ideal, not after a scalar extension. -/
theorem cubicLowerGradeInjective_polynomial_relation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin 4 → A) (hpy : p.eval₂ (algebraMap K A) y = 0) (n : ℕ)
    (hlow : ∀ a < n, Function.Injective (cubicGradeCoordinateEvaluation p hp a y hpy))
    (a : ℕ) (ha : a < n) (q : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous a) (hy : q.eval₂ (algebraMap K A) y = 0) :
    q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  let s : grading (equationIdeal p hp) a :=
    ⟨Ideal.Quotient.mk (equationIdeal p hp).toIdeal q,
      show Ideal.Quotient.mk (equationIdeal p hp).toIdeal q ∈
        (homogeneousSubmodule (Fin 4) K a).map
          (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap from
        ⟨q, hq, rfl⟩⟩
  have he : cubicGradeCoordinateEvaluation p hp a y hpy s = 0 := hy
  have hs : s = 0 := (hlow a ha)
    (he.trans (map_zero (cubicGradeCoordinateEvaluation p hp a y hpy)).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hs)

end

section
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Over the ORIGINAL residue field a product evaluates to zero only
when one factor does. Lower-grade injectivity then proves that its actual
quotient-grade product is zero. Nonprincipal curve components are not
claimed to be homogeneous ring factors. -/
theorem cubicLowerGradeInjective_gradeProduct_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (n : ℕ)
    (hlow : ∀ a < n, Function.Injective (cubicGradeCoordinateEvaluation p hp a y hpy))
    (a b : ℕ) (ha : a < n) (hb : b < n)
    (s : grading (equationIdeal p hp) a) (t : grading (equationIdeal p hp) b)
    (hvan : cubicCoordinateAlgebraEvaluation p hp y hpy (s.1 * t.1) = 0) :
    gradeSectionProduct (grading (equationIdeal p hp)) s t = 0 := by
  rw [map_mul] at hvan
  rcases mul_eq_zero.mp hvan with hs | ht
  · have hs' : cubicGradeCoordinateEvaluation p hp a y hpy s = 0 := hs
    have hs0 : s = 0 := (hlow a ha)
      (hs'.trans (map_zero (cubicGradeCoordinateEvaluation p hp a y hpy)).symm)
    apply Subtype.ext
    change s.1 * t.1 = 0
    rw [hs0]
    exact zero_mul _
  · have ht' : cubicGradeCoordinateEvaluation p hp b y hpy t = 0 := ht
    have ht0 : t = 0 := (hlow b hb)
      (ht'.trans (map_zero (cubicGradeCoordinateEvaluation p hp b y hpy)).symm)
    apply Subtype.ext
    change s.1 * t.1 = 0
    rw [ht0]
    exact mul_zero _

/-- An actual through-point polynomial nonzero modulo the cubic has no
homogeneous K-factorization whose two degrees are smaller than the first
through-point degree. This is ambient factor primitivity only. -/
theorem cubicLowerGradeInjective_no_homogeneousFactorization
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (n : ℕ)
    (hlow : ∀ a < n, Function.Injective (cubicGradeCoordinateEvaluation p hp a y hpy))
    (q : MvPolynomial (Fin 4) K) (hy : q.eval₂ (algebraMap K L) y = 0)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (a b : ℕ) (ha : a < n) (hb : b < n)
    (r t : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous a)
    (ht : t.IsHomogeneous b) (hfactor : q = r * t) : False := by
  let sr : grading (equationIdeal p hp) a :=
    ⟨Ideal.Quotient.mk (equationIdeal p hp).toIdeal r,
      show Ideal.Quotient.mk (equationIdeal p hp).toIdeal r ∈
        (homogeneousSubmodule (Fin 4) K a).map
          (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap from
        ⟨r, hr, rfl⟩⟩
  let st : grading (equationIdeal p hp) b :=
    ⟨Ideal.Quotient.mk (equationIdeal p hp).toIdeal t,
      show Ideal.Quotient.mk (equationIdeal p hp).toIdeal t ∈
        (homogeneousSubmodule (Fin 4) K b).map
          (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap from
        ⟨t, ht, rfl⟩⟩
  have he : cubicCoordinateAlgebraEvaluation p hp y hpy (sr.1 * st.1) = 0 := by
    change cubicCoordinateAlgebraEvaluation p hp y hpy
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal r *
        Ideal.Quotient.mk (equationIdeal p hp).toIdeal t) = 0
    rw [← map_mul]
    exact hfactor ▸ hy
  have hz := cubicLowerGradeInjective_gradeProduct_zero p hp y hpy n hlow
    a b ha hb sr st he
  have hv : Ideal.Quotient.mk (equationIdeal p hp).toIdeal r *
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal t = 0 :=
    congrArg Subtype.val hz
  rw [← map_mul] at hv
  exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp (hfactor.symm ▸ hv))

/-- The actual Hilbert window yields either a lower-degree through-point
section, or the honest minimal-degree injectivity needed for factor
primitivity. This does NOT replace the missing image-dimension either/or. -/
theorem cubicThroughPoint_lowerDegree_or_lowerGradeInjective [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    (∃ a < n, ∃ s : cubicThroughCoordinateSections p hp a y hpy, s ≠ 0) ∨
      (∀ a < n, Function.Injective (cubicGradeCoordinateEvaluation p hp a y hpy)) := by
  obtain ⟨a, han, s, hs, hlow⟩ :=
    exists_least_cubicThroughPoint_degree p hp hp0 n y hpy hsize
  rcases lt_or_eq_of_le han with ha | rfl
  · exact Or.inl ⟨a, ha, s, hs⟩
  · exact Or.inr hlow

end
end PfaffianDescent.Coray
end
