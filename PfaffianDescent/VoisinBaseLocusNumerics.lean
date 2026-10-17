import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.ProjectiveSpaceDimension

/-!
# Numerical contradiction in Voisin's base-locus argument

Claim 3.4 in Voisin's proof has one geometric input: a fixed curve of degree
at least three imposes at least `3 (l + 1)` independent conditions on
`H⁰(O_S(l + 1))`.  Once that input and very-generality of the length-`d`
subscheme are available, the contradiction is a finite-dimensional
calculation.  This file records that calculation separately, with no
unstated geometric assumptions.
-/

namespace PfaffianDescent

open Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If two nonnegative Hilbert functions are eventually affine-linear and
one is bounded above by the other, then its eventual slope is no larger.
This numerical lemma is intended for the bounded-Hilbert-polynomial step in
spreading a varying projective curve: the degree is the eventual first
difference, so a complete-intersection upper bound controls the curve degree. -/
theorem eventual_affine_hilbert_slope_le
    (f g : ℕ → ℕ) (N a b c d : ℕ)
    (hf : ∀ n, N ≤ n → f n = a * n + b)
    (hg : ∀ n, N ≤ n → g n = c * n + d)
    (hle : ∀ n, N ≤ n → f n ≤ g n) :
    a ≤ c := by
  by_contra h
  have hca : c + 1 ≤ a := by omega
  let n := max N (d + 1)
  have hn : N ≤ n := le_max_left _ _
  have hnd : d < n := by
    dsimp [n]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_right _ _)
  have hmul : (c + 1) * n ≤ a * n := Nat.mul_le_mul_right n hca
  have hsum : c * n + n + b ≤ c * n + d := by
    calc
      c * n + n + b ≤ a * n + b := by
        have hmul' : c * n + n ≤ a * n := by
          simpa [Nat.add_mul] using hmul
        exact Nat.add_le_add_right hmul' b
      _ = f n := (hf n hn).symm
      _ ≤ g n := hle n hn
      _ = c * n + d := hg n hn
  have hndb : n + b ≤ d := by omega
  omega

/-- Enlarging a homogeneous ideal can only lower the Hilbert function of its
graded quotient.  This is the degreewise comparison needed to bound a prime
curve containing the equations of a complete intersection. -/
theorem finrank_grading_antitone_of_homogeneousIdeal_le
    {K : Type u} [Field K]
    (I J : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    Module.finrank K (grading J d) ≤ Module.finrank K (grading I d) := by
  have hpiece : homogeneousIdealPiece I d ≤ homogeneousIdealPiece J d := by
    intro x hx
    exact hIJ hx
  have hdim := Submodule.finrank_mono hpiece
  have hI := finrank_homogeneousIdealPiece_add_finrank_grading I d
  have hJ := finrank_homogeneousIdealPiece_add_finrank_grading J d
  omega

/-- Two finite-dimensional subspaces whose intersection has dimension at
most one and whose sum is proper have total dimension at most the dimension
of the ambient space.  In Voisin's fixed/moving argument, the intersection
is the common product line, while a common zero makes the sum proper. -/
theorem finrank_add_le_finrank_of_inf_finrank_le_one_of_sup_ne_top
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U W : Submodule K V) (hinf : finrank K ↥(U ⊓ W) ≤ 1)
    (hsup : U ⊔ W ≠ ⊤) :
    finrank K U + finrank K W ≤ finrank K V := by
  have hsupLt : finrank K ↥(U ⊔ W) < finrank K V :=
    Submodule.finrank_lt hsup
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

/-- If two linear maps have a common distinguished value and equality of
their values forces both inputs to be the same scalar multiples of the
distinguished inputs, then their image subspaces meet exactly in the line
spanned by that common value.  For Voisin's fixed-component argument the
maps are multiplication by the defining sections of the complementary
divisors; the scalar-multiple condition is the cancellation statement coming
from the absence of a common curve component. -/
theorem range_inf_range_eq_span_of_common_line
    {K A B H : Type u} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup H] [Module K H]
    (f : A →ₗ[K] H) (g : B →ₗ[K] H) (a₀ : A) (b₀ : B)
    (hcommon : f a₀ = g b₀)
    (hcross : ∀ a b, f a = g b →
      ∃ c : K, a = c • a₀ ∧ b = c • b₀) :
    LinearMap.range f ⊓ LinearMap.range g =
      Submodule.span K {f a₀} := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := hq.1
    obtain ⟨b, hb⟩ := hq.2
    obtain ⟨c, hac, _hbc⟩ := hcross a b (ha.trans hb.symm)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [← ha, hac, map_smul]
  · intro hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    constructor
    · exact ⟨c • a₀, by simp⟩
    · exact ⟨c • b₀, by rw [map_smul, ← hcommon]⟩

/-- The numerical end of Voisin's Claim 3.4.

`ambient` and `twisted` are the dimensions of the sections of
`O_S(l + 1)` and `O_S(l + 1)(-D)`, respectively.  The four hypotheses are
exactly the restriction-rank estimate, the consequence of very-generality,
the lower degree-section bound, and the cubic-surface section jump. -/
theorem voisin_claim34_numerical_contradiction
    (l d previous ambient twisted : ℕ)
    (hrestriction : 3 * (l + 1) ≤ ambient - twisted)
    (hveryGeneral : d < twisted)
    (hlower : previous < d)
    (hjump : ambient = previous + 3 * (l + 1)) : False := by
  omega

/-- The numerical contradiction in the `s = 1` branch of Lemma 3.3.

When the section system has either two or three dimensions more than the
length of the generic subscheme, a mobile fixed curve would have to impose at
least three conditions while leaving all but at most two dimensions. -/
theorem voisin_singlePoint_mobile_curve_numerical_contradiction
    (d ambient twisted : ℕ)
    (hambient : ambient = d + 2 ∨ ambient = d + 3)
    (hveryGeneral : d < twisted)
    (hmobile : 3 ≤ ambient - twisted) : False := by
  omega

/-- Normalize the number of test points in Lemma 3.3 to the largest value
allowed by the section count.  This is the arithmetic behind Voisin's
reduction to `h⁰(I_Z(l+1)) = 2s` or `2s+1`: proving the generic-section
statement for this larger number of points also supplies it for the
original number by forgetting the extra marked points. -/
theorem voisin_normalize_test_point_count
    (sectionCount s : ℕ) (hs : 2 * s ≤ sectionCount) :
    ∃ s', s ≤ s' ∧
      (sectionCount = 2 * s' ∨ sectionCount = 2 * s' + 1) := by
  refine ⟨sectionCount / 2, ?_, ?_⟩
  · omega
  · omega

/-- The one-point branch after normalization occurs only when the section
count is two or three. -/
theorem voisin_normalized_singlePoint_sectionCount
    (sectionCount : ℕ)
    (h : sectionCount = 2 * 1 ∨ sectionCount = 2 * 1 + 1) :
    sectionCount = 2 ∨ sectionCount = 3 := by
  omega

/-- The section-space estimate in the disjoint-fixed-curve branch of Lemma
3.3.  A space of dimension at most `2s + 1 - (l + 2)` is strictly too small
to contain sections vanishing at a general set of `s ≥ 1` rank-two fibers. -/
theorem voisin_disjoint_fixed_curve_section_bound
    (l s sectionDim : ℕ) (hs : 0 < s)
    (hbound : sectionDim ≤ 2 * s + 1 - (l + 2)) : sectionDim < 2 * s := by
  omega

/-! ## The degree-eight fixed-component contradiction

For Lemma `leeffective`, the length is `d = h⁰(H) - 2`.  If a fixed curve
meets the generic length-`d` subscheme, symmetry forces it through all of the
generic points.  Its section space therefore has dimension at least `d + 1`,
while the moving part has dimension at least two.  The fixed-plus-moving
systems cannot fit in a proper subfamily of `|H|`.

If instead the fixed curve is disjoint from the generic subscheme, the
moving part has at least `d + 1` sections, contradicting the corresponding
very-ample bound `hMoving ≤ d`.  The following two lemmas record exactly the
arithmetic ends of those arguments. -/

/-- Numerical end of the branch where the fixed curve meets the generic
length-`d` subscheme.  The three assumptions are respectively the generic
point condition, the existence of a pencil after removing the fixed part,
and the dimension bound for a proper fixed-plus-moving subfamily of `|H|`. -/
theorem voisin_leeffective_fixedComponent_meets_numerical_contradiction
    (d hFixed hMoving : ℕ)
    (hgeneric : d + 1 ≤ hFixed)
    (hpencil : 2 ≤ hMoving)
    (hproper : hFixed + hMoving ≤ d + 2) : False := by
  omega

/-- Numerical end of the branch where the fixed curve is disjoint from the
generic length-`d` subscheme.  Here genericity gives at least `d + 1`
sections of the moving part, while very ampleness bounds that space by `d`. -/
theorem voisin_leeffective_fixedComponent_disjoint_numerical_contradiction
    (d hMoving : ℕ)
    (hgeneric : d + 1 ≤ hMoving)
    (hveryAmple : hMoving ≤ d) : False := by
  omega

section CubicDegreeTen

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The branch of `leeffective` in which a fixed curve meets the generic
length-eight subscheme has no numerical room on a cubic surface: the fixed
part contributes at least nine sections, the moving pencil at least two,
whereas the quadratic section space has dimension ten. -/
theorem voisin_degreeEight_fixedComponent_meets_numerical_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hFixed hMoving : ℕ)
    (hgeneric : 9 ≤ hFixed)
    (hpencil : 2 ≤ hMoving)
    (hproper : hFixed + hMoving ≤
      finrank K (grading (equationIdeal p hp) 2)) : False := by
  rw [cubicSurface_grade_two_finrank p hp hne] at hproper
  exact voisin_leeffective_fixedComponent_meets_numerical_contradiction
    8 hFixed hMoving hgeneric hpencil hproper

/-- The disjoint fixed-curve branch of `leeffective` is likewise
numerically impossible in degree eight once the geometric very-ample bound
places the moving section space below nine dimensions. -/
theorem voisin_degreeEight_fixedComponent_disjoint_numerical_contradiction
    (hMoving : ℕ)
    (hgeneric : 9 ≤ hMoving)
    (hveryAmple : hMoving ≤ 8) : False := by
  exact voisin_leeffective_fixedComponent_disjoint_numerical_contradiction
    8 hMoving hgeneric hveryAmple

/-- On an actual cubic surface the Hilbert-function jump in Claim 3.4 is
proved by `cubicSurface_grade_succ_finrank`.  Thus, for fixed curves of
degree at least two, the geometric restriction and very-generality estimates
are the only remaining inputs to the numerical contradiction. -/
theorem voisin_cubicSurface_claim34_numerical_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (l d twisted : ℕ) (hl : 2 ≤ l)
    (hrestriction : 3 * (l + 1) ≤
      finrank K (grading (equationIdeal p hp) (l + 1)) - twisted)
    (hveryGeneral : d < twisted)
    (hlower : finrank K (grading (equationIdeal p hp) l) < d) : False := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  have hm2 : 2 + m = m + 2 := by omega
  rw [hm2] at hrestriction hlower
  have hm3 : m + 2 + 1 = m + 3 := by omega
  rw [hm3] at hrestriction
  apply voisin_claim34_numerical_contradiction (m + 2) d
    (finrank K (grading (equationIdeal p hp) (m + 2)))
    (finrank K (grading (equationIdeal p hp) (m + 3))) twisted
  · exact hrestriction
  · exact hveryGeneral
  · exact hlower
  · exact cubicSurface_grade_succ_finrank p hp hne m

/-- The same numerical contradiction in Claim 3.4 holds for every
nonnegative twist.  The low-degree Hilbert-function jumps are now proved in
`cubicSurface_grade_succ_finrank_all`, so no artificial `l ≥ 2` restriction
is needed in the arithmetic part of Voisin's lemma. -/
theorem voisin_cubicSurface_claim34_numerical_contradiction_all
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (l d twisted : ℕ)
    (hrestriction : 3 * (l + 1) ≤
      finrank K (grading (equationIdeal p hp) (l + 1)) - twisted)
    (hveryGeneral : d < twisted)
    (hlower : finrank K (grading (equationIdeal p hp) l) < d) : False := by
  apply voisin_claim34_numerical_contradiction l d
    (finrank K (grading (equationIdeal p hp) l))
    (finrank K (grading (equationIdeal p hp) (l + 1))) twisted
  · exact hrestriction
  · exact hveryGeneral
  · exact hlower
  · exact cubicSurface_grade_succ_finrank_all p hp hne l

/-- The degree-ten instance of Claim 3.4 has no numerical room for a fixed
curve of degree at least three.  The two hypotheses are precisely the
geometric restriction-rank estimate and the very-general-subscheme bound;
the dimensions of quadratic and cubic sections are proved in
`CubicSurfaceSectionDimensions`. -/
theorem voisin_degreeTen_claim34_numerical_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (twisted : ℕ)
    (hrestriction : 9 ≤ finrank K (grading (equationIdeal p hp) 3) - twisted)
    (hveryGeneral : 11 < twisted) : False := by
  apply voisin_cubicSurface_claim34_numerical_contradiction
    p hp hne 2 11 twisted (by omega)
  · simpa using hrestriction
  · exact hveryGeneral
  · rw [cubicSurface_grade_two_finrank p hp hne]
    decide

/-- Claim 3.4 in the first residual construction is applied to the completed
length-sixteen configuration: a degree-ten datum is enlarged by two disjoint
degree-three line sections before the third cubic is selected.  Thus a fixed
curve of degree at least three is numerically impossible once very-generality
forces more than sixteen surviving sections. -/
theorem voisin_completedDegreeSixteen_claim34_numerical_contradiction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (twisted : ℕ)
    (hrestriction : 9 ≤ finrank K (grading (equationIdeal p hp) 3) - twisted)
    (hveryGeneral : 16 < twisted) : False := by
  apply voisin_cubicSurface_claim34_numerical_contradiction
    p hp hne 2 16 twisted (by omega)
  · simpa using hrestriction
  · exact hveryGeneral
  · rw [cubicSurface_grade_two_finrank p hp hne]
    decide

/-- The degree-ten specialization of the disjoint-fixed-curve estimate:
such a subsystem has dimension at most three, whereas vanishing at three
rank-two fibers requires six dimensions before the incidence argument. -/
theorem voisin_degreeTen_disjoint_fixed_curve_section_bound
    (sectionDim : ℕ) (hbound : sectionDim ≤ 3) : sectionDim < 2 * 3 := by
  apply voisin_disjoint_fixed_curve_section_bound 2 3 sectionDim (by decide)
  simpa using hbound

end CubicDegreeTen

end PfaffianDescent

namespace PfaffianDescent

/-- In the direct rank-two argument, the projectivized space of sections
vanishing along a rigid line or rigid degree-two divisor has dimension at
most three when the vector-space dimension is at most four. Its incidence
with triples of points therefore has dimension strictly below the dimension
six of the threefold symmetric product. This is the numerical endpoint;
the geometric proof that the incidence fibers have this dimension is a
separate input. -/
theorem voisin_serre_rigid_divisor_triple_incidence_dimension_lt
    (sectionSpaceDim : ℕ) (hsectionSpaceDim : sectionSpaceDim ≤ 4) :
    sectionSpaceDim - 1 < 6 := by
  omega

/-- For a conic pencil, the divisor parameter contributes one dimension.
If `k` marked points lie on a member of the pencil and the others lie in
the finite zero locus of the quotient section, the corresponding incidence
stratum has dimension at most `1 + k`, hence at most four for a triple. -/
theorem voisin_serre_conic_pencil_triple_incidence_dimension_le
    (k : ℕ) (hk : k ≤ 3) : 1 + k ≤ 4 := by
  omega

/-- Every stratum in the preceding conic-pencil count is too small to
dominate the six-dimensional space of triples of points. -/
theorem voisin_serre_conic_pencil_triple_incidence_dimension_lt
    (k : ℕ) (hk : k ≤ 3) : 1 + k < 6 := by
  have h := voisin_serre_conic_pencil_triple_incidence_dimension_le k hk
  omega

end PfaffianDescent

namespace PfaffianDescent

/-- The section-space bound in the rigid-divisor branch gives an actual
three-dimensional bound for the projective scheme parametrizing its
sections. -/
theorem voisin_serre_rigid_divisor_sectionParameterSpace_dimension_le_three
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (hpositive : 0 < Module.finrank K V)
    (hbound : Module.finrank K V ≤ 4) :
    topologicalKrullDim (finiteDimensionalProjectiveParameters K V) ≤ 3 :=
  finiteDimensionalProjectiveParameters_dimension_le_three K V hpositive hbound

end PfaffianDescent
