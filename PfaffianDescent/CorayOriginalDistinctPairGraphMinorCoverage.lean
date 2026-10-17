import PfaffianDescent.CorayOriginalWholePairChartLineMap

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Two distinct normalized points in an actual graph plane have nonzero
first-block minor. This is derived over the full coefficient ring; no
rank, minor nonvanishing or point-to-line outcome is supplied. -/
theorem normalizedDistinctGraphPair_selectedMinor_ne_zero001
    {B : Type u} [CommRing B]
    (f : (Fin 2 → B) →ₗ[B] (Fin 2 → B))
    (ell : ((Fin 2 → B) × (Fin 2 → B)) →ₗ[B] B)
    (x y : (Fin 2 → B) × (Fin 2 → B))
    (hx : f x.1 = x.2) (hy : f y.1 = y.2)
    (hEllx : ell x = 1) (hElly : ell y = 1) (hne : x ≠ y) :
    originalPairFirstBlockMinor x y ≠ 0 := by
  intro hMinor
  have hCross : x.1 0 * y.1 1 = x.1 1 * y.1 0 := by
    exact sub_eq_zero.mp hMinor
  have hFirst0 : x.1 0 • y.1 = y.1 0 • x.1 := by
    ext c
    fin_cases c
    · change x.1 0 * y.1 0 = y.1 0 * x.1 0
      exact mul_comm _ _
    · change x.1 0 * y.1 1 = y.1 0 * x.1 1
      simpa only [mul_comm] using hCross
  have hFirst1 : x.1 1 • y.1 = y.1 1 • x.1 := by
    ext c
    fin_cases c
    · change x.1 1 * y.1 0 = y.1 1 * x.1 0
      simpa only [mul_comm] using hCross.symm
    · change x.1 1 * y.1 1 = y.1 1 * x.1 1
      exact mul_comm _ _
  have hWhole0 : x.1 0 • y = y.1 0 • x := by
    apply Prod.ext
    · exact hFirst0
    · change x.1 0 • y.2 = y.1 0 • x.2
      rw [← hx, ← hy, ← map_smul, ← map_smul, hFirst0]
  have hWhole1 : x.1 1 • y = y.1 1 • x := by
    apply Prod.ext
    · exact hFirst1
    · change x.1 1 • y.2 = y.1 1 • x.2
      rw [← hx, ← hy, ← map_smul, ← map_smul, hFirst1]
  have h0 : x.1 0 = y.1 0 := by
    simpa only [map_smul, hEllx, hElly, smul_eq_mul, mul_one] using congrArg ell hWhole0
  have h1 : x.1 1 = y.1 1 := by
    simpa only [map_smul, hEllx, hElly, smul_eq_mul, mul_one] using congrArg ell hWhole1
  have hFirst : x.1 = y.1 := by
    ext c
    fin_cases c
    · exact h0
    · exact h1
  apply hne
  exact Prod.ext hFirst (by rw [← hx, ← hy, hFirst])

/-- The SAME selected original Grassmann chart covers every distinct
normalized pair of points in its actual plane. No change of line chart
or presumed nonzero determinant is needed. -/
theorem normalizedDistinctGrassmannPlanePair_selectedMinor_ne_zero001
    {B : Type u} [CommRing B] (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (T : Matrix (Fin 2) (Fin 2) B)
    (ell : ((Fin 2 → B) × (Fin 2 → B)) →ₗ[B] B)
    (x y : (Fin 2 → B) × (Fin 2 → B))
    (hx : x ∈ grassmannianChartSubmodule B rho T)
    (hy : y ∈ grassmannianChartSubmodule B rho T)
    (hEllx : ell x = 1) (hElly : ell y = 1) (hne : x ≠ y) :
    originalPairGrassmannMinor rho x y ≠ 0 := by
  let E := graphCoordinatePermutation B rho
  let f := Matrix.toLin' T
  change x ∈ f.graph.map (graphCoordinatePermutation B rho.symm).toLinearMap at hx
  change y ∈ f.graph.map (graphCoordinatePermutation B rho.symm).toLinearMap at hy
  rw [← graphCoordinatePermutation_symm] at hx hy
  have hxGraph : E x ∈ f.graph := (Submodule.mem_map_equiv (p := f.graph)).mp hx
  have hyGraph : E y ∈ f.graph := (Submodule.mem_map_equiv (p := f.graph)).mp hy
  let ellE := ell.comp E.symm.toLinearMap
  exact normalizedDistinctGraphPair_selectedMinor_ne_zero001 f ellE (E x) (E y)
    ((LinearMap.mem_graph_iff _ _).mp hxGraph).symm
    ((LinearMap.mem_graph_iff _ _).mp hyGraph).symm
    (by simpa only [ellE, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply] using hEllx)
    (by simpa only [ellE, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply] using hElly)
    (fun h => hne (E.injective h))

/-- The literal ORIGINAL ambient coordinate functional. -/
def originalAmbientCoordinateFunctional {B : Type u} [CommRing B] (j : Fin 4) :
    ((Fin 2 → B) × (Fin 2 → B)) →ₗ[B] B :=
  (LinearMap.proj j).comp (finiteProductCoordinateEquiv (R := B) 2 2).toLinearMap

private theorem originalAmbientCoordinateFunctional_blockVector001
    {B : Type u} [CommRing B] (j : Fin 4) (z : Fin 4 → B) :
    originalAmbientCoordinateFunctional j
      ((fun i => z (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
       (fun i => z (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) = z j := by
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  cases i with
  | inl i => simp [originalAmbientCoordinateFunctional, finiteProductCoordinateEquiv,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  | inr i => simp [originalAmbientCoordinateFunctional, finiteProductCoordinateEquiv,
      LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Every actual pair-ring point inherits both ORIGINAL chart normalizations.
Together with membership in the SAME Grassmann plane and actual distinctness,
this DERIVES nonvanishing of that chart's selected pair minor. -/
theorem cubicOriginalWholePairChart_distinct_plane_pair_selectedMinor_ne_zero001
    {K M : Type u} [Field K] [CommRing M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) M) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let B := R ⊗[K] R
    let xy := cubicOriginalWholePairChartAmbientVectors p hp j
    ∀ h : B →+* M,
    let x := graphCoefficientMap h xy.1
    let y := graphCoefficientMap h xy.2
    x ∈ grassmannianChartSubmodule M rho T →
    y ∈ grassmannianChartSubmodule M rho T → x ≠ y →
      originalPairGrassmannMinor rho x y ≠ 0 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let B := R ⊗[K] R
  let xy := cubicOriginalWholePairChartAmbientVectors p hp j
  dsimp only
  intro h
  let x := graphCoefficientMap h xy.1
  let y := graphCoefficientMap h xy.2
  intro hx hy hne
  have hEllx : originalAmbientCoordinateFunctional j x = 1 := by
    change originalAmbientCoordinateFunctional j
      ((fun i => h (chartCoordinate (equationIdeal p hp) j
          (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)) ⊗ₜ[K] (1 : R))),
       (fun i => h (chartCoordinate (equationIdeal p hp) j
          (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)) ⊗ₜ[K] (1 : R)))) = 1
    rw [originalAmbientCoordinateFunctional_blockVector001 j
      (fun i : Fin 4 => h (chartCoordinate (equationIdeal p hp) j i ⊗ₜ[K] (1 : R)))]
    rw [chartCoordinate_self, ← Algebra.TensorProduct.one_def, map_one]
  have hElly : originalAmbientCoordinateFunctional j y = 1 := by
    change originalAmbientCoordinateFunctional j
      ((fun i => h ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j
          (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i)))),
       (fun i => h ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j
          (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))))) = 1
    rw [originalAmbientCoordinateFunctional_blockVector001 j
      (fun i : Fin 4 => h ((1 : R) ⊗ₜ[K] chartCoordinate (equationIdeal p hp) j i))]
    rw [chartCoordinate_self, ← Algebra.TensorProduct.one_def, map_one]
  exact normalizedDistinctGrassmannPlanePair_selectedMinor_ne_zero001 rho T
    (originalAmbientCoordinateFunctional j) x y hx hy hEllx hElly hne

end PfaffianDescent.Coray
