import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.VoisinSectionLinearAlgebra
import AllCharacteristics.HomogeneousProjective

/-!
# Dimensions of sections on a cubic surface

Voisin's numerical hypotheses use
`h⁰(S, O_S(2)) = 10` and `h⁰(S, O_S(3)) = 19`.  This file proves the
corresponding statements for the actual graded homogeneous coordinate ring of
a nonzero cubic in four variables.  The proof identifies the kernel in degree
`d + 3` with multiplication by the cubic, not with a dimension postulate.
-/

namespace PfaffianDescent
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u

section
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev CubicSurfaceHomogeneous (K : Type u) [Field K] (d : ℕ) :=
  homogeneousSubmodule (Fin 4) K d

/-- Projection of degree-`d` equations to the homogeneous coordinate ring of
the cubic surface. -/
noncomputable def cubicSurfaceProjection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d : ℕ) :
    CubicSurfaceHomogeneous K d →ₗ[K] CoordinateRing (equationIdeal p hp) :=
  (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap.comp
    (CubicSurfaceHomogeneous K d).subtype

lemma cubicSurfaceProjection_range
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d : ℕ) :
    LinearMap.range (cubicSurfaceProjection p hp d) = grading (equationIdeal p hp) d := by
  rw [cubicSurfaceProjection, LinearMap.range_comp, Submodule.range_subtype]
  rfl

/-- Multiplication by the defining cubic on homogeneous pieces. -/
noncomputable def cubicSurfaceRelation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (d : ℕ) :
    CubicSurfaceHomogeneous K d →ₗ[K] CubicSurfaceHomogeneous K (d + 3) where
  toFun q := ⟨q.val * p, q.property.mul hp⟩
  map_add' a b := by
    apply Subtype.ext
    exact add_mul a.val b.val p
  map_smul' r a := by
    apply Subtype.ext
    exact smul_mul_assoc r a.val p

lemma cubicSurfaceRelation_injective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (d : ℕ) :
    Function.Injective (cubicSurfaceRelation p hp d) := by
  intro a b hab
  apply Subtype.ext
  exact mul_right_cancel₀ hne (congrArg Subtype.val hab)

/-- In every degree at least three, the only equations killed in the cubic
coordinate ring are homogeneous multiples of the defining cubic. -/
theorem cubicSurfaceRelation_range_eq_projection_ker
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (d : ℕ) :
    LinearMap.range (cubicSurfaceRelation p hp d) =
      LinearMap.ker (cubicSurfaceProjection p hp (d + 3)) := by
  apply le_antisymm
  · rintro v ⟨q, rfl⟩
    change Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q.val * p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_singleton p)
  · intro v hv
    change Ideal.Quotient.mk (equationIdeal p hp).toIdeal v.val = 0 at hv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
    change v.val ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hqp : q * p = v.val := by
      rw [mul_comm]
      exact hq.symm
    have hqh : q.IsHomogeneous d := homogeneous_of_mul_right hp hne (by
      rw [hqp]
      exact v.property)
    exact ⟨⟨q, hqh⟩, Subtype.ext hqp⟩

/-- Below degree three, projection to the cubic coordinate ring is injective. -/
theorem cubicSurfaceProjection_injective_of_lt_three
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (d : ℕ) (hd : d < 3) : Function.Injective (cubicSurfaceProjection p hp d) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  change Ideal.Quotient.mk (equationIdeal p hp).toIdeal v.val = 0 at hv
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hv
  change v.val ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hqp : q * p = v.val := by
    rw [mul_comm]
    exact hq.symm
  have hq0 : q = 0 := eq_zero_of_mul_homogeneous_lt hp hne (by
    rw [hqp]
    exact v.property) hd
  apply Subtype.ext
  rw [← hqp, hq0, zero_mul]
  rfl

/-- In every degree at least three, the homogeneous coordinate ring of a
cubic surface has the expected Hilbert function.  This is the exact
section-count formula used when Voisin's base-locus argument varies the
degree of a fixed curve. -/
theorem cubicSurface_grade_add_three_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (d : ℕ) :
    finrank K (grading (equationIdeal p hp) (d + 3)) =
      (d + 6).choose 3 - (d + 3).choose 3 := by
  have hdim := (cubicSurfaceProjection p hp (d + 3)).finrank_range_add_finrank_ker
  rw [cubicSurfaceProjection_range,
    ← cubicSurfaceRelation_range_eq_projection_ker p hp hne d,
    LinearMap.finrank_range_of_inj (cubicSurfaceRelation_injective p hp hne d),
    four_variable_homogeneous_finrank,
    four_variable_homogeneous_finrank] at hdim
  simpa [Nat.add_assoc] using Nat.eq_sub_of_add_eq hdim

/-- The Hilbert-function formula for every nonnegative degree on a cubic
surface.  In degrees below three the defining cubic creates no relation; in
higher degrees the relation space is exactly its homogeneous multiples. -/
theorem cubicSurface_grade_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (n : ℕ) :
    finrank K (grading (equationIdeal p hp) n) =
      (n + 3).choose 3 - n.choose 3 := by
  by_cases hn : n < 3
  · rw [← cubicSurfaceProjection_range,
      LinearMap.finrank_range_of_inj
        (cubicSurfaceProjection_injective_of_lt_three p hp hne n hn),
      four_variable_homogeneous_finrank,
      Nat.choose_eq_zero_of_lt hn, Nat.sub_zero]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    have hd : 3 + d = d + 3 := by omega
    rw [hd, cubicSurface_grade_add_three_finrank p hp hne d]

/-- The quadratic section space on a cubic surface has dimension ten. -/
theorem cubicSurface_grade_two_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    finrank K (grading (equationIdeal p hp) 2) = 10 := by
  rw [cubicSurface_grade_finrank p hp hne 2]
  decide

/-- The cubic section space on a cubic surface has dimension nineteen. -/
theorem cubicSurface_grade_three_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    finrank K (grading (equationIdeal p hp) 3) = 19 := by
  rw [cubicSurface_grade_finrank p hp hne 3]
  decide

/-- The constant section space of a cubic surface has dimension one. -/
theorem cubicSurface_grade_zero_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    finrank K (grading (equationIdeal p hp) 0) = 1 := by
  rw [cubicSurface_grade_finrank p hp hne 0]
  decide

/-- The linear section space of a cubic surface has dimension four. -/
theorem cubicSurface_grade_one_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    finrank K (grading (equationIdeal p hp) 1) = 4 := by
  rw [cubicSurface_grade_finrank p hp hne 1]
  decide

/-- Consecutive section spaces in degrees at least two differ by `3n` in
degree `n`.  This supplies the Hilbert-function jump in Voisin's Claim 3.4
from the actual cubic surface coordinate ring. -/
theorem cubicSurface_grade_succ_finrank
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (d : ℕ) :
    finrank K (grading (equationIdeal p hp) (d + 3)) =
      finrank K (grading (equationIdeal p hp) (d + 2)) + 3 * (d + 3) := by
  cases d with
  | zero =>
      rw [show 0 + 3 = 3 by omega, show 0 + 2 = 2 by omega,
        cubicSurface_grade_three_finrank p hp hne,
        cubicSurface_grade_two_finrank p hp hne]
  | succ d =>
      rw [show (d + 1) + 3 = d + 4 by omega,
        show (d + 1) + 2 = d + 3 by omega,
        cubicSurface_grade_add_three_finrank p hp hne (d + 1),
        cubicSurface_grade_add_three_finrank p hp hne d]
      simp only [Nat.add_succ, Nat.choose_succ_succ,
        Nat.choose_one_right, Nat.choose_zero_right]
      omega

/-- Consecutive graded pieces of the cubic-surface coordinate ring have the
Riemann--Roch jump `3(l + 1)` in every nonnegative degree.  The low-degree
cases are separate because no cubic relation occurs there; the higher-degree
case is `cubicSurface_grade_succ_finrank`. -/
theorem cubicSurface_grade_succ_finrank_all
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) (l : ℕ) :
    finrank K (grading (equationIdeal p hp) (l + 1)) =
      finrank K (grading (equationIdeal p hp) l) + 3 * (l + 1) := by
  rcases l with _ | _ | l
  · rw [show 0 + 1 = 1 by omega,
      cubicSurface_grade_zero_finrank p hp hne,
      cubicSurface_grade_one_finrank p hp hne]
  · rw [show 1 + 1 = 2 by omega,
      cubicSurface_grade_one_finrank p hp hne,
      cubicSurface_grade_two_finrank p hp hne]
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      cubicSurface_grade_succ_finrank p hp hne l

/-- The cubic-section count has the strict margin needed to make a rank-two
section vanish at three fibers after imposing a length-eleven subscheme. -/
theorem cubicSurface_rankTwo_cubic_sections_strict
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    2 * 3 < finrank K (grading (equationIdeal p hp) 3) - 11 := by
  rw [cubicSurface_grade_three_finrank p hp hne]
  norm_num

/-- The numerical input in Voisin's rank-two step is now an actual section
selection theorem for the cubic surface.  Once the rank-two construction
identifies its section space with the cubic sections vanishing on a
length-eleven subscheme, a nonzero section vanishing at three rank-two fibers
follows without any additional dimension assumption. -/
theorem exists_rankTwo_section_vanishing_of_cubicSurface_degree_eleven
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hE : finrank K E = finrank K (grading (equationIdeal p hp) 3) - 11)
    (ev : E →ₗ[K] (Fin 3 → Fin 2 → K)) :
    ∃ e : E, e ≠ 0 ∧ ev e = 0 := by
  apply exists_rankTwo_section_vanishing 3 ev
  rw [hE]
  exact cubicSurface_rankTwo_cubic_sections_strict p hp hne

/-- The same rank-two section selection needs only the lower bound on the
section space supplied by imposing a degree-eleven subscheme.  This is the
form used in Voisin's Proposition 3.2: no equality of the evaluation kernel
with the expected dimension is required. -/
theorem exists_rankTwo_section_vanishing_of_cubicSurface_degree_eleven_of_le
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hE : finrank K (grading (equationIdeal p hp) 3) - 11 ≤ finrank K E)
    (ev : E →ₗ[K] (Fin 3 → Fin 2 → K)) :
    ∃ e : E, e ≠ 0 ∧ ev e = 0 := by
  apply exists_rankTwo_section_vanishing 3 ev
  have hsections := cubicSurface_rankTwo_cubic_sections_strict p hp hne
  omega

/-- The degree-eleven count leaves two independent sections after imposing
three rank-two evaluation conditions.  These are the two generators of
Voisin's pencil; the later geometric argument is responsible only for the
regularity and zero-dimensionality of their zero schemes. -/
theorem exists_linearIndependent_rankTwo_sections_vanishing_of_cubicSurface_degree_eleven_of_le
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hE : finrank K (grading (equationIdeal p hp) 3) - 11 ≤ finrank K E)
    (ev : E →ₗ[K] (Fin 3 → Fin 2 → K)) :
    ∃ v : Fin 2 → E, LinearIndependent K v ∧ ∀ i, ev (v i) = 0 := by
  apply exists_linearIndependent_pair_mem_ker_of_finrank_target_lt ev
  rw [rankTwo_evaluation_target_finrank]
  have hE' := hE
  rw [cubicSurface_grade_three_finrank p hp hne] at hE'
  norm_num at hE'
  omega

/-- Equality with the expected degree-eleven section count is a special case
of the lower-bound form used by the rank-two construction. -/
theorem exists_linearIndependent_rankTwo_sections_vanishing_of_cubicSurface_degree_eleven
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hE : finrank K E = finrank K (grading (equationIdeal p hp) 3) - 11)
    (ev : E →ₗ[K] (Fin 3 → Fin 2 → K)) :
    ∃ v : Fin 2 → E, LinearIndependent K v ∧ ∀ i, ev (v i) = 0 := by
  apply exists_linearIndependent_rankTwo_sections_vanishing_of_cubicSurface_degree_eleven_of_le
    p hp hne _ ev
  omega

/-- All four numerical hypotheses used in Voisin's degree-ten argument.  The
first and fourth are the two instances of Lemma 3.6; the middle pair are the
two inequalities in Proposition 3.2 for `(l,d,s) = (2,11,3)`. -/
structure VoisinDegreeTenNumerics
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop where
  cubicResidualBound :
    16 ≤ finrank K (grading (equationIdeal p hp) 3) - 2
  rankTwoNoQuadrics :
    finrank K (grading (equationIdeal p hp) 2) < 11
  rankTwoCubicSections :
    2 * 3 ≤ finrank K (grading (equationIdeal p hp) 3) - 11
  quadricResidualBound :
    8 ≤ finrank K (grading (equationIdeal p hp) 2) - 2

/-- The degree-ten numerical hypotheses follow from the two proved section
dimensions; no cohomology dimension is left as an assumption. -/
theorem voisinDegreeTenNumerics
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    VoisinDegreeTenNumerics p hp := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [cubicSurface_grade_two_finrank p hp hne,
      cubicSurface_grade_three_finrank p hp hne] <;> omega

/-- The numerical hypotheses for the subsequent `11 ≤ d ≤ 13` branch of
Voisin's cubic-surface reduction are consequences of the actual Hilbert
function: a degree-`d` datum exceeds the quadratic section space, and the
cubic section space retains six conditions for three rank-two fibers. -/
theorem cubicSurface_vectorBundle_numerics_degree_eleven_to_thirteen
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (d : ℕ) (hd_lower : 11 ≤ d) (hd_upper : d ≤ 13) :
    finrank K (grading (equationIdeal p hp) 2) < d ∧
      2 * 3 ≤ finrank K (grading (equationIdeal p hp) 3) - d := by
  rw [cubicSurface_grade_two_finrank p hp hne,
    cubicSurface_grade_three_finrank p hp hne]
  omega

end
end PfaffianDescent
