import PfaffianDescent.CorayOriginalPairLineMinorMap

noncomputable section
namespace PfaffianDescent.Coray
universe u
set_option autoImplicit false

/-- An actual graph plane containing both original vectors determines
exactly the derived selected-minor matrix. No presumed point-to-line equality
or equality of matrices is supplied. -/
theorem originalPairMinorGraphMatrix_eq_givenGraphMatrix001
    {B : Type u} [CommRing B] (x y : (Fin 2 → B) × (Fin 2 → B))
    (u : B) (hMinor : originalPairFirstBlockMinor x y * u = 1)
    (T : Matrix (Fin 2) (Fin 2) B)
    (hx : Matrix.toLin' T x.1 = x.2) (hy : Matrix.toLin' T y.1 = y.2) :
    originalPairMinorGraphMatrix x y u = T := by
  let f := Matrix.toLin' (originalPairMinorGraphMatrix x y u)
  let g := Matrix.toLin' T
  have hSpan : Submodule.span B ({x, y} : Set ((Fin 2 → B) × (Fin 2 → B))) ≤ g.graph := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (LinearMap.mem_graph_iff _ _).mpr hx.symm
    · obtain rfl := Set.mem_singleton_iff.mp hz
      exact (LinearMap.mem_graph_iff _ _).mpr hy.symm
  have hGraph : f.graph ≤ g.graph := by
    change (Matrix.toLin' (originalPairMinorGraphMatrix x y u)).graph ≤ g.graph
    rw [originalPairMinorGraphMatrix_graph_eq_span001 x y u hMinor]
    exact hSpan
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hv : (v, f v) ∈ f.graph := (LinearMap.mem_graph_iff _ _).mpr rfl
  exact (LinearMap.mem_graph_iff _ _).mp (hGraph hv)

/-- The literal minor-derived matrix commutes with coefficient maps.
This retains the SAME original vectors and actual inverse image. -/
theorem originalPairMinorGraphMatrix_map001
    {B C : Type u} [CommRing B] [CommRing C] (phi : B →+* C)
    (x y : (Fin 2 → B) × (Fin 2 → B)) (u : B) :
    (originalPairMinorGraphMatrix x y u).map phi =
      originalPairMinorGraphMatrix (graphCoefficientMap phi x) (graphCoefficientMap phi y) (phi u) := by
  funext i c
  change phi (if c = 0 then u * (x.2 i * y.1 1 - y.2 i * x.1 1)
    else u * (y.2 i * x.1 0 - x.2 i * y.1 0)) =
    (if c = 0 then phi u * (phi (x.2 i) * phi (y.1 1) - phi (y.2 i) * phi (x.1 1))
    else phi u * (phi (y.2 i) * phi (x.1 0) - phi (x.2 i) * phi (y.1 0)))
  by_cases hc : c = 0
  · rw [if_pos hc, if_pos hc, map_mul, map_sub, map_mul, map_mul]
  · rw [if_neg hc, if_neg hc, map_mul, map_sub, map_mul, map_mul]

/-- Actual coefficient specialization of the selected-minor chart gives
the SAME prescribed graph matrix whenever both actual original vectors
belong to that graph. Its inverse relation is DERIVED by mapping the original
minor-unit identity. -/
theorem originalPairMinorGraphMatrix_map_eq_givenGraphMatrix001
    {B C : Type u} [CommRing B] [CommRing C] (phi : B →+* C)
    (x y : (Fin 2 → B) × (Fin 2 → B)) (u : B)
    (hMinor : originalPairFirstBlockMinor x y * u = 1)
    (T : Matrix (Fin 2) (Fin 2) C)
    (hx : Matrix.toLin' T (graphCoefficientMap phi x).1 = (graphCoefficientMap phi x).2)
    (hy : Matrix.toLin' T (graphCoefficientMap phi y).1 = (graphCoefficientMap phi y).2) :
    (originalPairMinorGraphMatrix x y u).map phi = T := by
  have hMinorMap : originalPairFirstBlockMinor (graphCoefficientMap phi x) (graphCoefficientMap phi y) =
      phi (originalPairFirstBlockMinor x y) := by
    change phi (x.1 0) * phi (y.1 1) - phi (x.1 1) * phi (y.1 0) =
      phi (x.1 0 * y.1 1 - x.1 1 * y.1 0)
    rw [map_sub, map_mul, map_mul]
  have hMinorC : originalPairFirstBlockMinor (graphCoefficientMap phi x) (graphCoefficientMap phi y) * phi u = 1 := by
    rw [hMinorMap, ← map_mul, hMinor, map_one]
  rw [originalPairMinorGraphMatrix_map001]
  exact originalPairMinorGraphMatrix_eq_givenGraphMatrix001 _ _ _ hMinorC T hx hy

end PfaffianDescent.Coray
