import PfaffianDescent.GoodIsotropicSplitting
import PfaffianDescent.GoodThirdBlockForm
import PfaffianDescent.GoodFiber

namespace PfaffianDescent
open Module
section
variable {K : Type*} [Field K]

/-- A line whose first coordinate is nonzero is the graph of a unique scalar. -/
lemma line_mem_iff_coordinate_ratio (L : Submodule K (Fin 2 → K))
    (hdim : finrank K L = 1) (v : Fin 2 → K) (hv : v ∈ L) (ha : v 0 ≠ 0)
    (y : Fin 2 → K) : y ∈ L ↔ y 1 = (v 1 / v 0) * y 0 := by
  have hvne : v ≠ 0 := by intro h; exact ha (congrFun h 0)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hvne,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    change c * v 1 = (v 1 / v 0) * (c * v 0)
    field_simp [ha]
  · intro hy
    refine ⟨y 0 / v 0, ?_⟩
    ext j
    fin_cases j
    · change (y 0 / v 0) * v 0 = y 0
      exact div_mul_cancel₀ _ ha
    · change (y 0 / v 0) * v 1 = y 1
      rw [hy]
      ring

end
section
variable (R : Type*) [CommRing R]

/-- The affine graph chart with one scalar slope in each two-dimensional block. -/
def goodBlockGraph (u : Fin 3 → R) : Submodule R (Fin 3 → Fin 2 → R) where
  carrier := {x | ∀ i, x i 1 = u i * x i 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro i
    simp only [Pi.add_apply]
    rw [hx i, hy i, mul_add]
  smul_mem' c x hx := by
    intro i
    change c * x i 1 = u i * (c * x i 0)
    rw [hx i]
    ring

lemma mem_goodBlockGraph (u : Fin 3 → R) (x : Fin 3 → Fin 2 → R) :
    x ∈ goodBlockGraph R u ↔ ∀ i, x i 1 = u i * x i 0 := Iff.rfl

end
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Every common isotropic three-space for the displayed triple lies in the affine
chart used in the note. This proves coverage for all field-valued points. -/
theorem goodCommonIsotropic_exists_affine_graph
    (W : Submodule K (Fin 3 → Fin 2 → K)) (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0)
    (h2 : ∀ x ∈ W, ∀ y ∈ W, goodThirdBlockForm K x y = 0) :
    ∃ u : Fin 3 → K, W = goodBlockGraph K u ∧ GoodFiberEquations (u 0) (u 1) (u 2) := by
  let L := goodBlockSubmodule K (Fin 2 → K) W
  have hL (i : Fin 3) : finrank K (L i) = 1 :=
    goodCommonIsotropic_block_finrank W hdim h0 h1 i
  let b (i : Fin 3) := finBasisOfFinrankEq K (L i) (hL i)
  let v (i : Fin 3) : Fin 2 → K := (b i 0).1
  have hv (i : Fin 3) : v i ∈ L i := (b i 0).2
  have hvW (i : Fin 3) : Pi.single i (v i) ∈ W := hv i
  have hvne (i : Fin 3) : v i ≠ 0 := by
    intro hz
    apply (b i).ne_zero 0
    exact Subtype.ext hz
  have hne (i : Fin 3) : v i 0 ≠ 0 ∨ v i 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hvne i
    ext j
    fin_cases j
    · exact hn.1
    · exact hn.2
  have h01 : v 0 0 * v 1 0 + v 0 1 * v 1 1 = 0 := by
    simpa only [goodThirdBlockForm_pair01] using h2 _ (hvW 0) _ (hvW 1)
  have h02 : v 0 0 * v 2 0 + v 0 1 * v 2 1 = 0 := by
    simpa only [goodThirdBlockForm_pair02] using h2 _ (hvW 0) _ (hvW 2)
  have h12 : v 1 0 * v 2 0 + 2 * v 1 1 * v 2 1 = 0 := by
    simpa only [goodThirdBlockForm_pair12] using h2 _ (hvW 1) _ (hvW 2)
  have ha : ∀ i, v i 0 ≠ 0 := goodFiber_affine_chart
    (fun i => v i 0) (fun i => v i 1) hne h01 h02 h12
  let u : Fin 3 → K := fun i => v i 1 / v i 0
  have hmem (i : Fin 3) (y : Fin 2 → K) :
      y ∈ L i ↔ y 1 = u i * y 0 :=
    line_mem_iff_coordinate_ratio (L i) (hL i) (v i) (hv i) (ha i) y
  refine ⟨u, ?_, ?_⟩
  · ext x
    constructor
    · intro hx i
      apply (hmem i (x i)).mp
      exact goodBlockProjection_mem K (Fin 2 → K)
        (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))) W
        (goodCommonIsotropic_invariant W hdim h0 h1) i hx
    · intro hx
      rw [← goodBlockProjection_sum K (Fin 2 → K) x]
      exact W.sum_mem (fun i _ => (hmem i (x i)).mpr (hx i))
  · change 1 + (v 0 1 / v 0 0) * (v 1 1 / v 1 0) = 0 ∧
      1 + (v 0 1 / v 0 0) * (v 2 1 / v 2 0) = 0 ∧
      1 + 2 * (v 1 1 / v 1 0) * (v 2 1 / v 2 0) = 0
    refine ⟨?_, ?_, ?_⟩
    · field_simp [ha 0, ha 1]
      simpa using h01
    · field_simp [ha 0, ha 2]
      simpa using h02
    · field_simp [ha 1, ha 2]
      simpa using h12

end
end PfaffianDescent
