import PfaffianDescent.GoodIsotropicAffineChart

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R]

/-- Independent interchange of the two coordinates in each symplectic plane. -/
def goodBlockCoordinateSwap (ε : Fin 3 → Bool) :
    (Fin 3 → Fin 2 → R) ≃ₗ[R] (Fin 3 → Fin 2 → R) where
  toFun x i := if ε i then ![x i 1, x i 0] else x i
  invFun x i := if ε i then ![x i 1, x i 0] else x i
  left_inv x := by
    funext i j
    cases h : ε i <;> fin_cases j <;> simp [h]
  right_inv x := by
    funext i j
    cases h : ε i <;> fin_cases j <;> simp [h]
  map_add' x y := by
    funext i j
    cases h : ε i <;> fin_cases j <;> simp [h]
  map_smul' c x := by
    funext i j
    cases h : ε i <;> fin_cases j <;> simp [h]

/-- One of the eight standard affine charts of the product of three projective lines. -/
def goodBlockMixedGraph (ε : Fin 3 → Bool) (u : Fin 3 → R) :
    Submodule R (Fin 3 → Fin 2 → R) :=
  (goodBlockGraph R u).comap (goodBlockCoordinateSwap R ε).toLinearMap

lemma mem_goodBlockMixedGraph (ε : Fin 3 → Bool) (u : Fin 3 → R)
    (x : Fin 3 → Fin 2 → R) :
    x ∈ goodBlockMixedGraph R ε u ↔
      ∀ i, if ε i then x i 0 = u i * x i 1 else x i 1 = u i * x i 0 := by
  change (∀ i, (goodBlockCoordinateSwap R ε x) i 1 = u i * (goodBlockCoordinateSwap R ε x) i 0) ↔ _
  apply forall_congr'
  intro i
  cases h : ε i <;> simp [goodBlockCoordinateSwap, h]

lemma goodBlockMixedGraph_map_swap (ε : Fin 3 → Bool) (u : Fin 3 → R) :
    (goodBlockMixedGraph R ε u).map (goodBlockCoordinateSwap R ε).toLinearMap = goodBlockGraph R u :=
  Submodule.map_comap_eq_of_surjective (goodBlockCoordinateSwap R ε).surjective _

end
section
variable {K : Type*} [Field K]

lemma line_mem_iff_second_coordinate_ratio (L : Submodule K (Fin 2 → K))
    (hdim : finrank K L = 1) (v : Fin 2 → K) (hv : v ∈ L) (hb : v 1 ≠ 0)
    (y : Fin 2 → K) : y ∈ L ↔ y 0 = (v 0 / v 1) * y 1 := by
  have hvne : v ≠ 0 := by intro h; exact hb (congrFun h 1)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hvne,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    change c * v 0 = (v 0 / v 1) * (c * v 1)
    field_simp [hb]
  · intro hy
    refine ⟨y 1 / v 1, ?_⟩
    ext j
    fin_cases j
    · change (y 1 / v 1) * v 0 = y 0
      rw [hy]
      ring
    · change (y 1 / v 1) * v 1 = y 1
      exact div_mul_cancel₀ _ hb

lemma line_has_standard_chart (L : Submodule K (Fin 2 → K)) (hdim : finrank K L = 1) :
    ∃ b : Bool, ∃ u : K, ∀ y : Fin 2 → K,
      y ∈ L ↔ if b then y 0 = u * y 1 else y 1 = u * y 0 := by
  let v : Fin 2 → K := (finBasisOfFinrankEq K L hdim 0).1
  have hv : v ∈ L := (finBasisOfFinrankEq K L hdim 0).2
  have hvne : v ≠ 0 := by
    intro h
    exact (finBasisOfFinrankEq K L hdim).ne_zero 0 (Subtype.ext h)
  by_cases ha : v 0 = 0
  · have hb : v 1 ≠ 0 := by
      intro hb
      apply hvne
      funext j
      fin_cases j
      · exact ha
      · exact hb
    exact ⟨true, v 0 / v 1, fun y => line_mem_iff_second_coordinate_ratio L hdim v hv hb y⟩
  · exact ⟨false, v 1 / v 0, fun y => line_mem_iff_coordinate_ratio L hdim v hv ha y⟩

end
section
variable {K : Type*} [Field K] [CharZero K]

/-- The first two isotropic forms' field-valued points are covered by all eight product charts. -/
theorem goodCommonPair_exists_standard_chart
    (W : Submodule K (Fin 3 → Fin 2 → K)) (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0) :
    ∃ ε : Fin 3 → Bool, ∃ u : Fin 3 → K, W = goodBlockMixedGraph K ε u := by
  let L := goodBlockSubmodule K (Fin 2 → K) W
  have hL (i : Fin 3) : finrank K (L i) = 1 := goodCommonIsotropic_block_finrank W hdim h0 h1 i
  choose ε u hu using fun i => line_has_standard_chart (L i) (hL i)
  refine ⟨ε, u, ?_⟩
  ext x
  rw [mem_goodBlockMixedGraph]
  constructor
  · intro hx i
    exact (hu i (x i)).mp (goodBlockProjection_mem K (Fin 2 → K)
      (isUnit_iff_ne_zero.mpr (by norm_num)) W (goodCommonIsotropic_invariant W hdim h0 h1) i hx)
  · intro hx
    rw [← goodBlockProjection_sum K (Fin 2 → K) x]
    exact W.sum_mem (fun i _ => (hu i (x i)).mpr (hx i))

end
end PfaffianDescent
