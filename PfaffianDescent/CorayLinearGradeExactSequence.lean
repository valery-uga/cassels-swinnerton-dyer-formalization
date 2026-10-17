import PfaffianDescent.CorayComponentHilbertFunctionBound
import PfaffianDescent.CorayFiniteProjectiveHilbertStabilization
import PfaffianDescent.HomogeneousProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual linear-equation grade exact sequence and finite-cut curve linearity

The maps use literal quotient classes of the actual polynomial H. Exactness
is derived by projection of actual ideal-sum representatives. Prime injectivity
is derived from H not belonging to the actual prime. The generic finite-cut
criterion uses native finiteness of the SAME hyperplane section; the original
p/q caller deriving that finiteness is a separate forthcoming leaf.
SOURCE ONLY / UNVERIFIED; no compiler run by this worker.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplication by the literal class of H in the actual component ring. -/
def componentLinearGradeMul
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (m : ℕ) :
    grading C m →ₗ[K] grading C (m + 1) :=
  PfaffianDescent.homogeneousGradeMul (grading C)
    (show Ideal.Quotient.mk C.toIdeal H ∈ grading C 1 from ⟨H, hH, rfl⟩) m

/-- Actual primeness and literal noncontainment imply grade injectivity. -/
theorem componentLinearGradeMul_injective
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1)
    (hnot : H ∉ C.toIdeal) (m : ℕ) :
    Function.Injective (componentLinearGradeMul C H hH m) := by
  have hz : Ideal.Quotient.mk C.toIdeal H ≠ 0 := by
    intro hzero
    exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  intro x y hxy
  have hmul := congrArg Subtype.val hxy
  change x.1 * Ideal.Quotient.mk C.toIdeal H =
    y.1 * Ideal.Quotient.mk C.toIdeal H at hmul
  exact Subtype.ext (mul_right_cancel₀ hz hmul)

/-- The kernel of the actual degreewise hyperplane quotient is EXACTLY
multiplication by H, without saturation or an exactness hypothesis. -/
theorem componentLinearGradeMul_range_eq_ker
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (m : ℕ) :
    LinearMap.range (componentLinearGradeMul C H hH m) =
      LinearMap.ker (homogeneousCoordinateQuotientGradeMap C
        (C ⊔ equationIdeal H hH) le_sup_left (m + 1)) := by
  let S := C ⊔ equationIdeal H hH
  let hCS : C.toIdeal ≤ S.toIdeal := le_sup_left
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change (Ideal.Quotient.factorₐ K hCS)
      (x.1 * Ideal.Quotient.mk C.toIdeal H) = 0
    rw [map_mul]
    have hz : (Ideal.Quotient.factorₐ K hCS)
        (Ideal.Quotient.mk C.toIdeal H) = 0 := by
      change Ideal.Quotient.mk S.toIdeal H = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_right : (equationIdeal H hH).toIdeal ≤ S.toIdeal)
        (Ideal.subset_span (Set.mem_singleton H))
    rw [hz, mul_zero]
  · intro y hy
    obtain ⟨q, hqhom, hq⟩ := y.2
    have hzero := congrArg Subtype.val hy
    change (Ideal.Quotient.factorₐ K hCS) y.1 = 0 at hzero
    rw [← hq] at hzero
    change Ideal.Quotient.mk S.toIdeal q = 0 at hzero
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    change q ∈ C.toIdeal ⊔ Ideal.span ({H} : Set (MvPolynomial (Fin 4) K)) at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hb
    have hdecomp : q = homogeneousComponent (m + 1) a +
        H * homogeneousComponent m s := by
      calc
        q = homogeneousComponent (m + 1) q :=
          (homogeneousComponent_eq_self hqhom).symm
        _ = homogeneousComponent (m + 1) (a + H * s) := by rw [← hs, hab]
        _ = homogeneousComponent (m + 1) a + H * homogeneousComponent m s := by
          rw [map_add]
          have hindex : m + 1 = 1 + m := by omega
          rw [hindex, PfaffianDescent.homogeneousComponent_mul_left hH m]
    have hazero : Ideal.Quotient.mk C.toIdeal (homogeneousComponent (m + 1) a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (homogeneousComponent_mem_of_mem C.isHomogeneous ha (m + 1))
    refine ⟨⟨Ideal.Quotient.mk C.toIdeal (homogeneousComponent m s),
      ⟨homogeneousComponent m s, homogeneousComponent_mem m s, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk C.toIdeal (homogeneousComponent m s) *
      Ideal.Quotient.mk C.toIdeal H = y.1
    calc
      _ = Ideal.Quotient.mk C.toIdeal (H * homogeneousComponent m s) := by
        rw [map_mul, mul_comm]
      _ = Ideal.Quotient.mk C.toIdeal
          (homogeneousComponent (m + 1) a + H * homogeneousComponent m s) := by
        rw [map_add, hazero, zero_add]
      _ = Ideal.Quotient.mk C.toIdeal q := congrArg _ hdecomp.symm
      _ = y.1 := hq

/-- Actual prime hyperplane quotient gives the consecutive-grade rank relation. -/
theorem componentLinearGrade_hilbertFunction_recurrence
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1)
    (hnot : H ∉ C.toIdeal) (m : ℕ) :
    finrank K (grading C (m + 1)) = finrank K (grading C m) +
      finrank K (grading (C ⊔ equationIdeal H hH) (m + 1)) := by
  letI : ∀ d, Module.Finite K (grading C d) := PfaffianDescent.polynomialQuotientGrade_finite C
  let F := componentLinearGradeMul C H hH m
  let Q := homogeneousCoordinateQuotientGradeMap C (C ⊔ equationIdeal H hH)
    le_sup_left (m + 1)
  have hF := F.finrank_range_add_finrank_ker
  have hQ := Q.finrank_range_add_finrank_ker
  have hinj : Function.Injective F := componentLinearGradeMul_injective C H hH hnot m
  have hsurj : Function.Surjective Q :=
    homogeneousCoordinateQuotientGradeMap_surjective C (C ⊔ equationIdeal H hH)
      le_sup_left (m + 1)
  have hker : LinearMap.range F = LinearMap.ker Q :=
    componentLinearGradeMul_range_eq_ker C H hH m
  rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero] at hF
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hker] at hQ
  omega

/-- A genuine finite actual hyperplane section gives an affine Hilbert function
whose slope is its SAME native scheme rank; no linear-polynomial premise. -/
theorem primeComponent_hilbertFunction_affine_of_finite_linearSection
    [Infinite K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (hnot : H ∉ C.toIdeal)
    [IsFinite (toBase (C ⊔ equationIdeal H hH))] :
    ∃ N : ℕ, ∀ t : ℕ,
      finrank K (grading C (N + t)) = finrank K (grading C N) +
        t * finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) := by
  obtain ⟨N, hN⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank
    (C ⊔ equationIdeal H hH)
  refine ⟨N, ?_⟩
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep := componentLinearGrade_hilbertFunction_recurrence C H hH hnot (N + t)
    have hsection := hN (N + t + 1) (by omega)
    rw [hsection, ih] at hstep
    have hindex : finrank K (grading C (N + Nat.succ t)) =
        finrank K (grading C (N + t + 1)) :=
      (congrArg (fun d => finrank K (grading C d)) (Nat.add_assoc N t 1)).symm
    simpa only [Nat.succ_mul, Nat.add_assoc] using hindex.trans hstep

end PfaffianDescent.Coray
