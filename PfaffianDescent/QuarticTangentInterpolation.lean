import PfaffianDescent.QuarticNetLinearAlgebra
import PfaffianDescent.HomogeneousDimensions
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.FinCases

/-!
# Cubic interpolation at four tangent double points

This is the homogeneous degree-three interpolation argument used in Section 4
of `2-proofs.tex`.  It identifies the cubics vanishing at four coordinate
first-order points with the span of the twelve linear multiples of a net of
quadrics, once those multiples are independent.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

section
variable {K : Type*} [Field K]

/-- The first-order point at the `i`th coordinate vertex with tangent
coefficients given by row `i` of `U`. -/
def tangentDualPoint (U : Fin 4 → Fin 4 → K) (i j : Fin 4) : DualNumber K :=
  TrivSqZeroExt.inl (if i = j then 1 else 0) + TrivSqZeroExt.inr (U i j)

/-- Restriction of homogeneous cubics to the four tangent double points. -/
noncomputable def tangentCubicRestriction (U : Fin 4 → Fin 4 → K) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (Fin 4 → DualNumber K) :=
  LinearMap.pi fun i => (aeval (tangentDualPoint U i)).toLinearMap.domRestrict _

theorem tangentDualPoint_cube_eval (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (r i : Fin 4) :
    aeval (tangentDualPoint U r) (X i ^ 3 : MvPolynomial (Fin 4) K) =
      if r = i then 1 else 0 := by
  rcases eq_or_ne r i with rfl | hr
  · apply TrivSqZeroExt.ext <;>
      simp [tangentDualPoint, hdiag, pow_succ]
  · apply TrivSqZeroExt.ext <;>
      simp [tangentDualPoint, hr, pow_succ]

theorem tangentDualPoint_mixed_eval (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (r i j : Fin 4) (hij : i ≠ j) :
    aeval (tangentDualPoint U r) (X i ^ 2 * X j : MvPolynomial (Fin 4) K) =
      if r = i then inr (U i j) else 0 := by
  rcases eq_or_ne r i with rfl | hr
  · apply TrivSqZeroExt.ext <;>
      simp [tangentDualPoint, hdiag, hij, pow_two]
  · apply TrivSqZeroExt.ext <;>
      simp [tangentDualPoint, hr, pow_two]

noncomputable def cubicHermiteInterpolant (U : Fin 4 → Fin 4 → K) (j : Fin 4 → Fin 4)
    (w : Fin 4 → DualNumber K) : MvPolynomial (Fin 4) K :=
  ∑ i : Fin 4,
    (C (w i).fst * X i ^ 3 + C ((w i).snd / U i (j i)) * (X i ^ 2 * X (j i)))

theorem cubicHermiteInterpolant_homogeneous (U : Fin 4 → Fin 4 → K) (j : Fin 4 → Fin 4)
    (w : Fin 4 → DualNumber K) : (cubicHermiteInterpolant U j w).IsHomogeneous 3 := by
  unfold cubicHermiteInterpolant
  apply IsHomogeneous.sum
  intro i _
  exact ((isHomogeneous_X_pow i 3).C_mul _).add
    (((isHomogeneous_X_pow i 2).mul (isHomogeneous_X K (j i))).C_mul _)

theorem cubicHermiteInterpolant_eval (U : Fin 4 → Fin 4 → K) (j : Fin 4 → Fin 4)
    (hdiag : ∀ i, U i i = 0) (hn : ∀ i, U i (j i) ≠ 0)
    (w : Fin 4 → DualNumber K) (r : Fin 4) :
    aeval (tangentDualPoint U r) (cubicHermiteInterpolant U j w) = w r := by
  have hij (i : Fin 4) : i ≠ j i := by
    intro h
    apply hn i
    rw [← h, hdiag]
  simp only [cubicHermiteInterpolant, map_sum, map_add, map_mul, aeval_C,
    tangentDualPoint_cube_eval U hdiag,
    tangentDualPoint_mixed_eval U hdiag _ _ _ (hij _),
    mul_ite, mul_zero, mul_one, Finset.sum_add_distrib]
  simp [TrivSqZeroExt.algebraMap_eq_inl]
  apply TrivSqZeroExt.ext <;> simp
  field_simp [hn r]

theorem tangentCubicRestriction_surjective (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hn : ∀ i, ∃ j, U i j ≠ 0) :
    Function.Surjective (tangentCubicRestriction U) := by
  choose j hj using hn
  intro w
  refine ⟨⟨cubicHermiteInterpolant U j w,
    cubicHermiteInterpolant_homogeneous U j w⟩, ?_⟩
  funext i
  exact cubicHermiteInterpolant_eval U j hdiag hj w i

theorem tangentCubicRestriction_ker_finrank (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hn : ∀ i, ∃ j, U i j ≠ 0) :
    finrank K (LinearMap.ker (tangentCubicRestriction U)) = 12 := by
  let _ : FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 3)
  have h := (tangentCubicRestriction U).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tangentCubicRestriction_surjective U hdiag hn),
    finrank_top, four_variable_homogeneous_finrank] at h
  have hd : finrank K (Fin 4 → DualNumber K) = 8 := by
    change finrank K (Fin 4 → K × K) = 8
    simp [Module.finrank_pi_fintype, Module.finrank_prod]
  rw [hd] at h
  norm_num [Nat.choose] at h
  omega

/-- The twelve degree-three products of the three quadrics with the four
coordinate linear forms. -/
noncomputable def linearQuadricProducts (Q : Fin 3 → MvPolynomial (Fin 4) K) :
    Fin 3 × Fin 4 → MvPolynomial (Fin 4) K := fun ij => Q ij.1 * X ij.2

/-- The same products, recorded in the degree-three homogeneous submodule. -/
noncomputable def linearQuadricSections (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2) :
    Fin 3 × Fin 4 → MvPolynomial.homogeneousSubmodule (Fin 4) K 3 :=
  fun ij => ⟨linearQuadricProducts Q ij, (hQ ij.1).mul (isHomogeneous_X K ij.2)⟩

/-- A direct interpolation criterion for the cubic ideal membership needed in
Section 4.  The independence premise is discharged separately for each
concrete net of quadrics. -/
theorem cubic_ideal_membership_of_linear_products
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0) (hn : ∀ i, ∃ j, U i j ≠ 0)
    (Q : Fin 3 → MvPolynomial (Fin 4) K) (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hQvan : ∀ j i, aeval (tangentDualPoint U i) (Q j) = 0)
    (hind : LinearIndependent K (linearQuadricProducts Q))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i, aeval (tangentDualPoint U i) F = 0) :
    F ∈ Ideal.span (Set.range Q) := by
  let V := MvPolynomial.homogeneousSubmodule (Fin 4) K 3
  let S := Submodule.span K (Set.range (linearQuadricSections Q hQ))
  let T := LinearMap.ker (tangentCubicRestriction U)
  let _ : FiniteDimensional K V :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 3)
  have hTv : finrank K T = 12 := tangentCubicRestriction_ker_finrank U hdiag hn
  have hind' : LinearIndependent K (linearQuadricSections Q hQ) :=
    LinearIndependent.of_comp V.subtype hind
  have hS : finrank K S = 12 := by
    change finrank K (Submodule.span K (Set.range (linearQuadricSections Q hQ))) = 12
    rw [finrank_span_eq_card hind']
    rfl
  have hle : S ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    apply funext
    intro i
    change aeval (tangentDualPoint U i) (Q ij.1 * X ij.2) = 0
    rw [map_mul, hQvan, zero_mul]
  have heq : S = T := Submodule.eq_of_le_of_finrank_le hle (by rw [hTv, hS])
  have hFI : (⟨F, hF⟩ : V) ∈ S := by
    rw [heq]
    exact funext hvan
  have hSI : S ≤ ((Ideal.span (Set.range Q)).restrictScalars K).comap V.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self ij.1))
  exact hSI hFI

end
end QuarticNet
end PfaffianDescent
