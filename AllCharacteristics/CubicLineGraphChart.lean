import AllCharacteristics.CubicGraphLineDifferential
import AllCharacteristics.CubicCoordinatePermutation
import AllCharacteristics.CubicGraphLineDescentAssembly
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FieldSimp

/-! Any actual independent line frame admits one
of the six graph charts, after a ground permutation of ambient coordinates.
The formulas below normalize the selected two-by-two minor explicitly. -/

noncomputable section
namespace AllCharacteristics

open PfaffianDescent
open scoped BigOperators
universe u
variable {L : Type u} [Field L]

theorem cubicLine_exists_nonzero_minor
    (s b : Fin 4 → L) (hind : LinearIndependent L ![s, b]) :
    ∃ i j : Fin 4, s i * b j - s j * b i ≠ 0 := by
  by_contra h
  push Not at h
  have hs0 : s ≠ 0 := hind.ne_zero 0
  apply hs0
  funext i
  have hrel : ∑ k : Fin 2, (![-b i, s i] : Fin 2 → L) k • (![s, b] : Fin 2 → (Fin 4 → L)) k = 0 := by
    funext j
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change (-b i) * s j + s i * b j = 0
    linear_combination h i j
  have hi := Fintype.linearIndependent_iff.mp hind _ hrel 1
  exact hi

theorem cubicLine_exists_permutation_nonzero_first_minor
    (s b : Fin 4 → L) (hind : LinearIndependent L ![s, b]) :
    ∃ π : Equiv.Perm (Fin 4), s (π 0) * b (π 1) - s (π 1) * b (π 0) ≠ 0 := by
  obtain ⟨i, j, hij⟩ := cubicLine_exists_nonzero_minor s b hind
  have hij' : i ≠ j := by
    intro h
    subst j
    exact hij (sub_self _)
  have hinj : Function.Injective (![i, j] : Fin 2 → Fin 4) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun k : Fin 2 => Fin.castAdd 2 k) (![i, j] : Fin 2 → Fin 4)
    (Fin.castAdd_injective 2 2) hinj
  have h0 : π 0 = i := hπ 0
  have h1 : π 1 = j := hπ 1
  exact ⟨π, by simpa only [h0, h1] using hij⟩

def cubicLineFirstMinor (s b : Fin 4 → L) : L := s 0 * b 1 - s 1 * b 0

def cubicLineNormalizedSlope (s b : Fin 4 → L) : Fin 4 → L :=
  (b 1 / cubicLineFirstMinor s b) • s + (-(s 1 / cubicLineFirstMinor s b)) • b

def cubicLineNormalizedBase (s b : Fin 4 → L) : Fin 4 → L :=
  (-(b 0 / cubicLineFirstMinor s b)) • s + (s 0 / cubicLineFirstMinor s b) • b

theorem cubicLine_normalized_first_coordinates
    (s b : Fin 4 → L) (hminor : cubicLineFirstMinor s b ≠ 0) :
    cubicLineNormalizedSlope s b 0 = 1 ∧ cubicLineNormalizedSlope s b 1 = 0 ∧
    cubicLineNormalizedBase s b 0 = 0 ∧ cubicLineNormalizedBase s b 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [cubicLineNormalizedSlope, cubicLineNormalizedBase, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    field_simp [hminor] <;> simp only [cubicLineFirstMinor] <;> ring

def cubicLineNormalizedGraphCoordinates (s b : Fin 4 → L) : Fin 4 → L :=
  ![cubicLineNormalizedSlope s b 2, cubicLineNormalizedBase s b 2,
    cubicLineNormalizedSlope s b 3, cubicLineNormalizedBase s b 3]

theorem cubicLine_normalized_eq_graph
    (s b : Fin 4 → L) (hminor : cubicLineFirstMinor s b ≠ 0) :
    cubicLineNormalizedSlope s b = cubicGraphLineSlope (cubicLineNormalizedGraphCoordinates s b) ∧
    cubicLineNormalizedBase s b = cubicGraphLineBase (cubicLineNormalizedGraphCoordinates s b) := by
  have h := cubicLine_normalized_first_coordinates s b hminor
  constructor
  · funext i
    fin_cases i <;> simp [cubicGraphLineSlope, cubicLineNormalizedGraphCoordinates, h.1, h.2.1]
  · funext i
    fin_cases i <;> simp [cubicGraphLineBase, cubicLineNormalizedGraphCoordinates, h.2.2.1, h.2.2.2]

/-- The normalized graph remains in the original line, with explicit frame
coefficients. -/
theorem cubicLine_normalized_point_mem_original_span
    (s b : Fin 4 → L) (t : L) :
    ∃ u v : L, t • cubicLineNormalizedSlope s b + cubicLineNormalizedBase s b = u • s + v • b := by
  refine ⟨t * (b 1 / cubicLineFirstMinor s b) - b 0 / cubicLineFirstMinor s b,
    -(t * (s 1 / cubicLineFirstMinor s b)) + s 0 / cubicLineFirstMinor s b, ?_⟩
  funext i
  simp only [cubicLineNormalizedSlope, cubicLineNormalizedBase, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- An arbitrary vector on the line satisfies the normalized graph's first
normal equation. -/
theorem cubicLine_original_point_graph_relation
    (s b : Fin 4 → L) (hminor : cubicLineFirstMinor s b ≠ 0) (u v : L) :
    (u • s + v • b) 2 =
      cubicLineNormalizedSlope s b 2 * (u • s + v • b) 0 +
      cubicLineNormalizedBase s b 2 * (u • s + v • b) 1 := by
  simp only [cubicLineNormalizedSlope, cubicLineNormalizedBase, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hminor]
  simp only [cubicLineFirstMinor]
  ring

/-- Actual generic line exclusion, for arbitrary independent line frames.
This is precisely the pointwise no-contained-line property used in the
tangent/secant construction. Graph chart selection, coordinate-field
generation, coprimeness, scalar rigidity and field descent are all internal. -/
theorem cubicGeneric_no_contained_line_through
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra K L]
    (c : Cubic K 4) (x : Fin 4 → L) (hx : LinearIndependent K x)
    (hsmooth : ∀ (M : Type u) [Field M] (f : K →+* M) (y : Fin 4 → M),
      y ≠ 0 → (c.map f).eval y = 0 → ∃ d, (c.map f).mixed y d ≠ 0) :
    ∀ d : Fin 4 → L, LinearIndependent L ![x, d] →
      ∃ s t : L, (c.map (algebraMap K L)).eval (s • x + t • d) ≠ 0 := by
  intro d hind
  by_contra h
  push Not at h
  obtain ⟨π, hminor⟩ := cubicLine_exists_permutation_nonzero_first_minor x d hind
  let s' : Fin 4 → L := fun i => x (π i)
  let b' : Fin 4 → L := fun i => d (π i)
  let a := cubicLineNormalizedGraphCoordinates s' b'
  let c' := cubicCoordinatePermutation c π
  have hminor' : cubicLineFirstMinor s' b' ≠ 0 := hminor
  have hgraph := cubicLine_normalized_eq_graph s' b' hminor'
  have hline : ∀ t : K, (c'.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0 := by
    intro t
    rw [← hgraph.1, ← hgraph.2]
    obtain ⟨u, v, huv⟩ := cubicLine_normalized_point_mem_original_span s' b' (algebraMap K L t)
    rw [huv]
    calc
      (c'.map (algebraMap K L)).eval (u • s' + v • b') =
          (cubicCoordinatePermutation (c.map (algebraMap K L)) π).eval
            (fun i => (u • x + v • d) (π i)) := rfl
      _ = (c.map (algebraMap K L)).eval (u • x + v • d) :=
        cubicCoordinatePermutation_eval _ _ _
      _ = 0 := h u v
  have hx' : LinearIndependent K s' := hx.comp π π.injective
  have hsmooth' := cubicCoordinatePermutation_geometrically_nonsingular c π hsmooth
  have hnot := cubicGeneric_not_on_contained_graph c' s' a hx' hline hsmooth'
  apply hnot
  have hrel := cubicLine_original_point_graph_relation s' b' hminor' (1 : L) (0 : L)
  simpa only [a, cubicLineNormalizedGraphCoordinates, one_smul, zero_smul, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hrel

end AllCharacteristics
