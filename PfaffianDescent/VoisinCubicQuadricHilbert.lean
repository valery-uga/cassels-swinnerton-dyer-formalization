import PfaffianDescent.TwoGeneratorKoszul
import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.VoisinCurveHilbertDegreeBound
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hilbert slope of a cubic--quadric complete intersection

The quotient by a regular cubic and quadric in four variables has eventual
Hilbert function `6 n - 3`.  This supplies the complete-intersection slope
input needed to bound the degree of a fixed curve containing both equations.
-/

namespace PfaffianDescent
namespace CubicQuadricHilbert

open MvPolynomial Module CategoryTheory AlgebraicGeometry
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

noncomputable def cubicQuadricGradedComponent
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (n : ℕ) :
    Submodule K (CoordinateRing (cubicQuadricEquationHomogeneousIdeal p q hp hq)) :=
  grading (cubicQuadricEquationHomogeneousIdeal p q hp hq) n

noncomputable def cubicQuadricGradedFirst
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    FourHomogeneous K d →ₗ[K]
      FourHomogeneous K (d + 3) × FourHomogeneous K (d + 2) where
  toFun c :=
    (⟨-p * c.1, by
        change (-p * c.1).IsHomogeneous (d + 3)
        rw [Nat.add_comm d 3]
        exact hp.neg.mul c.2⟩,
     ⟨q * c.1, by
        change (q * c.1).IsHomogeneous (d + 2)
        rw [Nat.add_comm d 2]
        exact hq.mul c.2⟩)
  map_add' a b := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' a b := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_smul_comm]

noncomputable def cubicQuadricGradedLast
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    FourHomogeneous K (d + 3) × FourHomogeneous K (d + 2) →ₗ[K]
      FourHomogeneous K (d + 5) where
  toFun v := ⟨q * v.1.1 + p * v.2.1, by
    change (q * v.1.1 + p * v.2.1).IsHomogeneous (d + 5)
    apply IsHomogeneous.add
    · convert hq.mul v.1.2 using 1 <;> omega
    · convert hp.mul v.2.2 using 1 <;> omega⟩
  map_add' a b := by
    apply Subtype.ext
    change q * (a.1.1 + b.1.1) + p * (a.2.1 + b.2.1) =
      (q * a.1.1 + p * a.2.1) + (q * b.1.1 + p * b.2.1)
    ring
  map_smul' a b := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      RingHom.id_apply, mul_smul_comm, smul_add]

theorem cubicQuadricGradedFirst_injective
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hq0 : q ≠ 0) (d : ℕ) :
    Function.Injective (cubicQuadricGradedFirst p q hp hq d) := by
  intro a b hab
  have h := congrArg
    (fun v : FourHomogeneous K (d + 3) × FourHomogeneous K (d + 2) => v.2.1) hab
  exact Subtype.ext (mul_left_cancel₀ hq0 h)

theorem cubicQuadricGraded_exact
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q p) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedFirst p q hp hq d) =
      LinearMap.ker (cubicQuadricGradedLast p q hp hq d) := by
  apply le_antisymm
  · rintro v ⟨c, rfl⟩
    apply Subtype.ext
    change q * (-p * c.1) + p * (q * c.1) = 0
    ring
  · intro v hv
    have hv' : (v.1.1, v.2.1) ∈ LinearMap.ker (twoGeneratorLast q p) := by
      exact congrArg Subtype.val hv
    rw [← twoGenerator_exact hq0 hrel] at hv'
    obtain ⟨c, hc⟩ := hv'
    have hqmul : q * c = v.2.1 := congrArg Prod.snd hc
    have hpmul : -p * c = v.1.1 := congrArg Prod.fst hc
    have hch : c.IsHomogeneous d :=
      homogeneous_of_mul_right hq hq0 (by
        rw [mul_comm, hqmul]
        exact v.2.2)
    exact ⟨⟨c, hch⟩, Prod.ext (Subtype.ext hpmul) (Subtype.ext hqmul)⟩

noncomputable def cubicQuadricGradedProjection
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (n : ℕ) :
    FourHomogeneous K n →ₗ[K]
      CoordinateRing (cubicQuadricEquationHomogeneousIdeal p q hp hq) :=
  (Ideal.Quotient.mkₐ K
    (cubicQuadricEquationHomogeneousIdeal p q hp hq).toIdeal).toLinearMap.comp
      (FourHomogeneous K n).subtype

theorem cubicQuadricGradedProjection_range
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (n : ℕ) :
    LinearMap.range (cubicQuadricGradedProjection p q hp hq n) =
      cubicQuadricGradedComponent p q hp hq n := by
  change LinearMap.range
      ((Ideal.Quotient.mkₐ K
        (cubicQuadricEquationHomogeneousIdeal p q hp hq).toIdeal).toLinearMap.comp
          (FourHomogeneous K n).subtype) =
    (FourHomogeneous K n).map
      (Ideal.Quotient.mkₐ K
        (cubicQuadricEquationHomogeneousIdeal p q hp hq).toIdeal).toLinearMap
  rw [LinearMap.range_comp, Submodule.range_subtype]

theorem cubicQuadricGradedProjection_exact
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedLast p q hp hq d) =
      LinearMap.ker (cubicQuadricGradedProjection p q hp hq (d + 5)) := by
  apply le_antisymm
  · rintro v ⟨ab, rfl⟩
    change Ideal.Quotient.mk _ (q * ab.1.1 + p * ab.2.1) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hq_mem : q ∈ (cubicQuadricEquationHomogeneousIdeal p q hp hq).toIdeal := by
      rw [cubicQuadricEquationHomogeneousIdeal_toIdeal]
      exact Ideal.subset_span (by simp)
    have hp_mem : p ∈ (cubicQuadricEquationHomogeneousIdeal p q hp hq).toIdeal := by
      rw [cubicQuadricEquationHomogeneousIdeal_toIdeal]
      exact Ideal.subset_span (by simp)
    exact Ideal.add_mem _ (Ideal.mul_mem_right ab.1.1 _ hq_mem)
      (Ideal.mul_mem_right ab.2.1 _ hp_mem)
  · intro v hv
    change Ideal.Quotient.mk _ v.1 = 0 at hv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
    rw [cubicQuadricEquationHomogeneousIdeal_toIdeal] at hmem
    have hspan : v.1 ∈ Ideal.span ({q, p} : Set (MvPolynomial (Fin 4) K)) := by
      have hset : ({q, p} : Set (MvPolynomial (Fin 4) K)) = {p, q} := by
        ext x
        simp [or_comm]
      rw [hset]
      exact hmem
    rw [← twoGeneratorLast_range] at hspan
    obtain ⟨⟨a, b⟩, hab⟩ := hspan
    let a' := homogeneousComponent (d + 3) a
    let b' := homogeneousComponent (d + 2) b
    have hqa : homogeneousComponent (d + 5) (q * a) = q * a' := by
      rw [show d + 5 = 2 + (d + 3) by omega]
      exact homogeneousComponent_mul_left hq (d + 3)
    have hpb : homogeneousComponent (d + 5) (p * b) = p * b' := by
      rw [show d + 5 = 3 + (d + 2) by omega]
      exact homogeneousComponent_mul_left hp (d + 2)
    have hab' : q * a' + p * b' = v.1 := by
      have := congrArg (homogeneousComponent (d + 5)) hab
      change homogeneousComponent (d + 5) (q * a + p * b) = _ at this
      rw [map_add, hqa, hpb, homogeneousComponent_eq_self v.2] at this
      exact this
    refine ⟨(⟨a', homogeneousComponent_isHomogeneous _ _⟩,
      ⟨b', homogeneousComponent_isHomogeneous _ _⟩), ?_⟩
    apply Subtype.ext
    exact hab'

lemma four_homogeneous_finrank_cubic_quadric (d : ℕ) :
    finrank K (FourHomogeneous K d) = (d + 3).choose 3 := by
  rw [homogeneous_polynomial_finrank]
  have h : 4 + d - 1 = d + 3 := by omega
  rw [h]
  exact Nat.choose_symm_add

lemma cubic_quadric_choose_identity (d : ℕ) :
    6 * d + 27 + (d + 5).choose 3 + (d + 6).choose 3 =
      (d + 8).choose 3 + (d + 3).choose 3 := by
  simp only [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right,
    Nat.choose_zero_right]
  omega

/-- The cubic--quadric complete-intersection quotient has Hilbert function
`6 n - 3` from degree five onward. -/
theorem cubic_quadric_hilbert_slope_six
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q p) (d : ℕ) :
    finrank K (cubicQuadricGradedComponent p q hp hq (d + 5)) = 6 * d + 27 := by
  have hfirst := LinearMap.finrank_range_add_finrank_ker
    (cubicQuadricGradedFirst p q hp hq d)
  rw [LinearMap.ker_eq_bot.mpr
      (cubicQuadricGradedFirst_injective p q hp hq hq0 d),
    finrank_bot, add_zero] at hfirst
  have hlast := LinearMap.finrank_range_add_finrank_ker
    (cubicQuadricGradedLast p q hp hq d)
  rw [← cubicQuadricGraded_exact p q hp hq hq0 hrel d,
    hfirst, Module.finrank_prod] at hlast
  have hproj := LinearMap.finrank_range_add_finrank_ker
    (cubicQuadricGradedProjection p q hp hq (d + 5))
  rw [cubicQuadricGradedProjection_range,
    ← cubicQuadricGradedProjection_exact p q hp hq d] at hproj
  rw [four_homogeneous_finrank_cubic_quadric, four_homogeneous_finrank_cubic_quadric,
    four_homogeneous_finrank_cubic_quadric] at hlast
  rw [four_homogeneous_finrank_cubic_quadric] at hproj
  rw [four_homogeneous_finrank_cubic_quadric] at hfirst
  have hchoose := cubic_quadric_choose_identity d
  simp only [Nat.add_assoc] at hfirst hlast hproj
  linear_combination hproj - hlast - hchoose

theorem eventual_affine_hilbert_slope_cubic_quadric_completeIntersection
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q p) :
    ∀ n, 5 ≤ n →
      finrank K (grading
        (cubicQuadricEquationHomogeneousIdeal p q hp hq) n) = 6 * n - 3 := by
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := cubic_quadric_hilbert_slope_six p q hp hq hq0 hrel d
  have hlin : 6 * (d + 5) - 3 = 6 * d + 27 := by omega
  rw [Nat.add_comm 5 d]
  exact h

theorem fixedCurve_hilbert_degree_le_six
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q p)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hcontain : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal)
    (N c e : ℕ)
    (hC : ∀ n, N ≤ n → finrank K (grading C n) = c * n + e) :
    c ≤ 6 := by
  let I := cubicQuadricEquationHomogeneousIdeal p q hp hq
  let M := max N 5
  have hM : 5 ≤ M := le_max_right N 5
  have hMbig : 3 ≤ 6 * M := by omega
  have hI : ∀ n, 0 ≤ n → finrank K (grading I (M + n)) = 6 * n + (6 * M - 3) := by
    intro n hn
    have h := eventual_affine_hilbert_slope_cubic_quadric_completeIntersection
      p q hp hq hq0 hrel (M + n) (le_trans (le_max_right N 5) (Nat.le_add_right M n))
    rw [Nat.mul_add] at h
    change finrank K
      (grading (cubicQuadricEquationHomogeneousIdeal p q hp hq) (M + n)) = _
    calc
      _ = 6 * M + 6 * n - 3 := h
      _ = 6 * n + (6 * M - 3) := by omega
  have hcurve : ∀ n, 0 ≤ n → finrank K (grading C (M + n)) = c * n + (c * M + e) := by
    intro n hn
    have h := hC (M + n) (le_trans (le_max_left N 5) (Nat.le_add_right M n))
    simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using h
  have hle : ∀ n, 0 ≤ n → finrank K (grading C (M + n)) ≤ finrank K (grading I (M + n)) := by
    intro n hn
    exact finrank_grading_fixedCurve_le_cubicQuadric_quotient
      p q hp hq C hcontain (M + n)
  exact eventual_affine_hilbert_slope_le
    (fun n => finrank K (grading C (M + n)))
    (fun n => finrank K (grading I (M + n))) 0 c (c * M + e) 6 (6 * M - 3)
    hcurve hI hle

/-- Applying the Hilbert-slope estimate to the actual prime fixed divisor
produced by the degree-eight construction bounds its degree by six. The
remaining input is eventual affine growth for that particular homogeneous
prime curve. -/
theorem DegreeEightDivisorFixedSubschemeData.hilbert_degree_le_six
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (D : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp)
    (N c e : ℕ)
    (hHilbert : ∀ n, N ≤ n → finrank K (grading C n) = c * n + e) :
    c ≤ 6 := by
  rcases D with ⟨hq, -, hq0, hrel, -, -, -, -, -, hcontain, -, -⟩
  exact fixedCurve_hilbert_degree_le_six p q hp hq hq0 hrel.symm
    C hcontain N c e hHilbert

end CubicQuadricHilbert
end PfaffianDescent
