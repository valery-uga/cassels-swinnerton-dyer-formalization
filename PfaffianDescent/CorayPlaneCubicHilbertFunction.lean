import PfaffianDescent.HomogeneousProjection
import AllCharacteristics.HomogeneousProjective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/- SOURCE ONLY154; no compiler/options/limit changes. -/

/- Source snapshot: /private/tmp/cassels-coray-plane-cubic-hilbert-surviving-equation-source154/new/PfaffianDescent/CorayPlaneCubicHilbertFunction.lean -/
/-! SOURCE ONLY / UNVERIFIED154. Native Fin3 cubic Hilbert function from
literal homogeneous multiplication and the actual coordinate quotient. No
smoothness, integrality, Hilbert polynomial or growth certificate is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native monomial count in the literal three-variable homogeneous piece. -/
theorem threeVariable_homogeneous_finrank (d : ℕ) :
    finrank K (homogeneousSubmodule (Fin 3) K d) = (d + 2).choose 2 := by
  rw [PfaffianDescent.homogeneous_polynomial_finrank]
  have h : 3 + d - 1 = d + 2 := by omega
  rw [h]
  exact Nat.choose_symm_add

instance planeCubicCoordinateGrade_finite
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    Module.Finite K (grading (equationIdeal F hF) d) := by
  change Module.Finite K ((homogeneousSubmodule (Fin 3) K d).map
    (Ideal.Quotient.mkₐ K (equationIdeal F hF).toIdeal).toLinearMap)
  infer_instance

/-- Literal multiplication by the cubic in its actual homogeneous degrees. -/
def planeCubicHomogeneousMul
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    homogeneousSubmodule (Fin 3) K d →ₗ[K]
      homogeneousSubmodule (Fin 3) K (d + 3) where
  toFun a := ⟨F * a.val, by
    change (F * a.val).IsHomogeneous (d + 3)
    simpa only [Nat.add_comm] using hF.mul a.property⟩
  map_add' a b := Subtype.ext (by simp [mul_add])
  map_smul' c a := Subtype.ext (by simp [mul_smul_comm])

theorem planeCubicHomogeneousMul_injective
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) (d : ℕ) :
    Function.Injective (planeCubicHomogeneousMul F hF d) := by
  intro a b hab
  exact Subtype.ext (mul_left_cancel₀ hF0 (congrArg Subtype.val hab))

/-- The actual degree-d coordinate quotient projection, not an abstract
vector space with a prescribed Hilbert dimension. -/
def planeCubicCoordinateGradeProjection
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    homogeneousSubmodule (Fin 3) K d →ₗ[K] grading (equationIdeal F hF) d where
  toFun a := ⟨Ideal.Quotient.mk (equationIdeal F hF).toIdeal a.val,
    ⟨a.val, a.property, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := Subtype.ext
    (map_smul (Ideal.Quotient.mkₐ K (equationIdeal F hF).toIdeal) c a.val)

theorem planeCubicCoordinateGradeProjection_surjective
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    Function.Surjective (planeCubicCoordinateGradeProjection F hF d) := by
  rintro ⟨a, f, hfd, hf⟩
  exact ⟨⟨f, hfd⟩, Subtype.ext hf⟩

/-- Actual cubic relations in degree d+3 are exactly the image of literal
multiplication in degree d, proved by homogeneous projection of a preimage. -/
theorem planeCubicCoordinateGradeProjection_exact
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    LinearMap.range (planeCubicHomogeneousMul F hF d) =
      LinearMap.ker (planeCubicCoordinateGradeProjection F hF (d + 3)) := by
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial (Fin 3) K)))
      (F * b.val) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton F))
  · intro a ha
    have hzero := congrArg Subtype.val ha
    change Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial (Fin 3) K))) a.val = 0 at hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
    have hFb : F * b = a.val := hb.symm
    refine ⟨⟨homogeneousComponent d b, homogeneousComponent_isHomogeneous _ _⟩, ?_⟩
    apply Subtype.ext
    change F * homogeneousComponent d b = a.val
    have hproj : homogeneousComponent (d + 3) (F * b) = F * homogeneousComponent d b := by
      rw [show d + 3 = 3 + d from Nat.add_comm _ _]
      exact PfaffianDescent.homogeneousComponent_mul_left hF d
    rw [← hproj, hFb, homogeneousComponent_eq_self a.property]

/-- The native cubic quotient Hilbert recurrence follows from the actual
injective multiplication map and actual quotient exactness. -/
theorem planeCubicCoordinateGrade_finrank_add
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) (d : ℕ) :
    finrank K (grading (equationIdeal F hF) (d + 3)) +
      finrank K (homogeneousSubmodule (Fin 3) K d) =
      finrank K (homogeneousSubmodule (Fin 3) K (d + 3)) := by
  let M := planeCubicHomogeneousMul F hF d
  let P := planeCubicCoordinateGradeProjection F hF (d + 3)
  have hM := LinearMap.finrank_range_add_finrank_ker M
  have hP := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.ker_eq_bot.mpr (planeCubicHomogeneousMul_injective F hF hF0 d),
    finrank_bot, add_zero] at hM
  rw [LinearMap.range_eq_top.mpr (planeCubicCoordinateGradeProjection_surjective F hF (d + 3)),
    finrank_top, ← planeCubicCoordinateGradeProjection_exact F hF d, hM] at hP
  exact hP

/-- Three consecutive Pascal recurrences give the exact plane-cubic
monomial difference, without asymptotics or a polynomial-growth premise. -/
theorem planeCubic_choose_difference (d : ℕ) :
    (d + 5).choose 2 = (d + 2).choose 2 + 3 * (d + 3) := by
  simp only [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
  omega

theorem planeCubicCoordinateGrade_finrank_eq_three_mul_add_three
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) (d : ℕ) :
    finrank K (grading (equationIdeal F hF) (d + 3)) = 3 * (d + 3) := by
  have h := planeCubicCoordinateGrade_finrank_add F hF hF0 d
  rw [threeVariable_homogeneous_finrank, threeVariable_homogeneous_finrank] at h
  have hchoose := planeCubic_choose_difference d
  have hadd : d + 3 + 2 = d + 5 := by omega
  rw [hadd] at h
  omega

/-- Below cubic degree the actual projection has zero kernel: a nonzero
cubic cannot divide a nonzero homogeneous polynomial of smaller degree. -/
theorem planeCubicCoordinateGradeProjection_ker_eq_bot_of_lt_three
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (d : ℕ) (hd : d < 3) :
    LinearMap.ker (planeCubicCoordinateGradeProjection F hF d) = ⊥ := by
  apply bot_unique
  intro a ha
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change a.val = 0
  by_contra ha0
  have hzero := congrArg Subtype.val ha
  change Ideal.Quotient.mk (Ideal.span ({F} : Set (MvPolynomial (Fin 3) K))) a.val = 0 at hzero
  have hdiv : F ∣ a.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv ha0
  rw [hF.totalDegree hF0, a.property.totalDegree ha0] at hle
  omega

theorem planeCubicCoordinateGrade_finrank_eq_polynomial_of_lt_three
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (d : ℕ) (hd : d < 3) :
    finrank K (grading (equationIdeal F hF) d) = (d + 2).choose 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (planeCubicCoordinateGradeProjection F hF d)
  rw [LinearMap.range_eq_top.mpr (planeCubicCoordinateGradeProjection_surjective F hF d),
    finrank_top, planeCubicCoordinateGradeProjection_ker_eq_bot_of_lt_three F hF hF0 d hd,
    finrank_bot, add_zero, threeVariable_homogeneous_finrank] at h
  exact h

/-- Native exact positive-degree Hilbert function of the SAME nonzero cubic
in THREE variables. Smoothness and geometric integrality are unnecessary. -/
theorem planeCubicCoordinateGrade_finrank_eq_three_mul
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (d : ℕ) (hd : 1 ≤ d) :
    finrank K (grading (equationIdeal F hF) d) = 3 * d := by
  by_cases hlarge : 3 ≤ d
  · have heq : d - 3 + 3 = d := by omega
    have h := planeCubicCoordinateGrade_finrank_eq_three_mul_add_three F hF hF0 (d - 3)
    exact heq ▸ h
  · have h := planeCubicCoordinateGrade_finrank_eq_polynomial_of_lt_three F hF hF0 d (by omega)
    have hcases : d = 1 ∨ d = 2 := by omega
    rcases hcases with rfl | rfl <;> norm_num at h ⊢ <;> exact h

end PfaffianDescent.Coray
