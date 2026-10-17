import PfaffianDescent.GrassmannianHomogeneousFrame
import PfaffianDescent.GrassmannianFiniteType
import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import PfaffianDescent.VoisinSmoothCubicEliminatedChart
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open _root_.Matrix
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The literal selected two-coordinate determinant of two ORIGINAL
ambient vectors, before any localization or field extension. -/
def originalPairFirstBlockMinor {B : Type u} [CommRing B]
    (x y : (Fin 2 → B) × (Fin 2 → B)) : B :=
  x.1 0 * y.1 1 - x.1 1 * y.1 0

/-- Actual graph coordinates obtained by inverting only the selected
minor. They are valid over the full coefficient ring, including nilpotents. -/
def originalPairMinorGraphMatrix {B : Type u} [CommRing B]
    (x y : (Fin 2 → B) × (Fin 2 → B)) (u : B) : Matrix (Fin 2) (Fin 2) B :=
  fun i c => if c = 0 then u * (x.2 i * y.1 1 - y.2 i * x.1 1)
    else u * (y.2 i * x.1 0 - x.2 i * y.1 0)

/-- The derived matrix sends both original first coordinate blocks to
both original second blocks. No line/spanning outcome is a premise. -/
theorem originalPairMinorGraphMatrix_maps_both001
    {B : Type u} [CommRing B] (x y : (Fin 2 → B) × (Fin 2 → B))
    (u : B) (hMinor : originalPairFirstBlockMinor x y * u = 1) :
    Matrix.toLin' (originalPairMinorGraphMatrix x y u) x.1 = x.2 ∧
      Matrix.toLin' (originalPairMinorGraphMatrix x y u) y.1 = y.2 := by
  constructor
  · ext i
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change u * (x.2 i * y.1 1 - y.2 i * x.1 1) * x.1 0 +
      u * (y.2 i * x.1 0 - x.2 i * y.1 0) * x.1 1 = x.2 i
    calc
      _ = (originalPairFirstBlockMinor x y * u) * x.2 i := by
        dsimp only [originalPairFirstBlockMinor]
        ring
      _ = x.2 i := by rw [hMinor, one_mul]
  · ext i
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change u * (x.2 i * y.1 1 - y.2 i * x.1 1) * y.1 0 +
      u * (y.2 i * x.1 0 - x.2 i * y.1 0) * y.1 1 = y.2 i
    calc
      _ = (originalPairFirstBlockMinor x y * u) * y.2 i := by
        dsimp only [originalPairFirstBlockMinor]
        ring
      _ = y.2 i := by rw [hMinor, one_mul]

/-- The actual graph is EXACTLY the module span of the two original
vectors whenever the selected minor has its actual inverse. -/
theorem originalPairMinorGraphMatrix_graph_eq_span001
    {B : Type u} [CommRing B] (x y : (Fin 2 → B) × (Fin 2 → B))
    (u : B) (hMinor : originalPairFirstBlockMinor x y * u = 1) :
    (Matrix.toLin' (originalPairMinorGraphMatrix x y u)).graph =
      Submodule.span B ({x, y} : Set ((Fin 2 → B) × (Fin 2 → B))) := by
  obtain ⟨hx, hy⟩ := originalPairMinorGraphMatrix_maps_both001 x y u hMinor
  let f := Matrix.toLin' (originalPairMinorGraphMatrix x y u)
  change f x.1 = x.2 at hx
  change f y.1 = y.2 at hy
  apply le_antisymm
  · intro z hz
    have hzEq : z.2 = f z.1 := (LinearMap.mem_graph_iff _ _).mp hz
    let alpha := u * (z.1 0 * y.1 1 - z.1 1 * y.1 0)
    let beta := u * (x.1 0 * z.1 1 - x.1 1 * z.1 0)
    have hFirst : alpha • x.1 + beta • y.1 = z.1 := by
      ext c
      fin_cases c
      · change alpha * x.1 0 + beta * y.1 0 = z.1 0
        calc
          _ = (originalPairFirstBlockMinor x y * u) * z.1 0 := by
            dsimp only [alpha, beta, originalPairFirstBlockMinor]
            ring
          _ = z.1 0 := by rw [hMinor, one_mul]
      · change alpha * x.1 1 + beta * y.1 1 = z.1 1
        calc
          _ = (originalPairFirstBlockMinor x y * u) * z.1 1 := by
            dsimp only [alpha, beta, originalPairFirstBlockMinor]
            ring
          _ = z.1 1 := by rw [hMinor, one_mul]
    have hWhole : alpha • x + beta • y = z := by
      apply Prod.ext
      · exact hFirst
      · change alpha • x.2 + beta • y.2 = z.2
        calc
          _ = f (alpha • x.1 + beta • y.1) := by
            simp only [map_add, map_smul, hx, hy]
          _ = f z.1 := congrArg f hFirst
          _ = z.2 := hzEq.symm
    rw [← hWhole]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ alpha (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ beta (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (LinearMap.mem_graph_iff _ _).mpr hx.symm
    · have hzy : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact (LinearMap.mem_graph_iff _ _).mpr hy.symm

/-- Selected original minor, with the original Grassmann chart index
retained. This is an actual regular function on the WHOLE pair ring. -/
def originalPairGrassmannMinor {B : Type u} [CommRing B]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x y : (Fin 2 → B) × (Fin 2 → B)) : B :=
  originalPairFirstBlockMinor (graphCoordinatePermutation B rho x) (graphCoordinatePermutation B rho y)

/-- The actual ORIGINAL-K point of the WHOLE Grassmannian on the literal
selected-minor principal open. No presumed line map/dominance is supplied. -/
def originalPairMinorOpenToGrassmann {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x y : (Fin 2 → B) × (Fin 2 → B)) :
    Spec (.of (Localization.Away (originalPairGrassmannMinor rho x y))) ⟶ grassmannianScheme K 2 2 :=
  let d := originalPairGrassmannMinor rho x y
  let C := Localization.Away d
  let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
  let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
  grassmannianChartEvaluation K
    (originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)) ≫ grassmannianChartι K rho

/-- Its base morphism is the literal ORIGINAL K localization coefficient
map. No transported scalar action is substituted. -/
theorem originalPairMinorOpenToGrassmann_originalBaseSquare001
    {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x y : (Fin 2 → B) × (Fin 2 → B)) :
    originalPairMinorOpenToGrassmann (K := K) rho x y ≫ grassmannianToBase K 2 2 =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away (originalPairGrassmannMinor rho x y)))) := by
  dsimp only [originalPairMinorOpenToGrassmann]
  rw [Category.assoc, grassmannianChartι_toBase, grassmannianChartEvaluation_toBase]

/-- Both ORIGINAL vectors lie in, and generate, the actual plane of the
constructed line on the literal minor open. Localization supplies the
inverse; no field/nonzero/rank outcome certificate is a premise. -/
theorem originalPairMinorOpen_graph_eq_originalSpan001
    {B : Type u} [CommRing B] (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (x y : (Fin 2 → B) × (Fin 2 → B)) :
    let d := originalPairGrassmannMinor rho x y
    let C := Localization.Away d
    let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
    let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
    grassmannianChartSubmodule C rho
      (originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)) =
      Submodule.span C
        ({graphCoefficientMap (algebraMap B C) x, graphCoefficientMap (algebraMap B C) y} :
          Set ((Fin 2 → C) × (Fin 2 → C))) := by
  let d := originalPairGrassmannMinor rho x y
  let C := Localization.Away d
  let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
  let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
  have hMinorMap : originalPairFirstBlockMinor xC yC = algebraMap B C d := by
    change algebraMap B C ((graphCoordinatePermutation B rho x).1 0) *
      algebraMap B C ((graphCoordinatePermutation B rho y).1 1) -
      algebraMap B C ((graphCoordinatePermutation B rho x).1 1) *
      algebraMap B C ((graphCoordinatePermutation B rho y).1 0) = algebraMap B C d
    dsimp only [d, originalPairGrassmannMinor, originalPairFirstBlockMinor]
    rw [map_sub, map_mul, map_mul]
  have hMinor : originalPairFirstBlockMinor xC yC * IsLocalization.Away.invSelf d = 1 := by
    rw [hMinorMap]
    exact IsLocalization.Away.mul_invSelf d
  change ((Matrix.toLin' (originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d))).graph.map
    (graphCoordinatePermutation C rho.symm).toLinearMap) = _
  rw [originalPairMinorGraphMatrix_graph_eq_span001 xC yC (IsLocalization.Away.invSelf d) hMinor, Submodule.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, LinearEquiv.coe_coe]
  have hXback : graphCoordinatePermutation C rho.symm xC = graphCoefficientMap (algebraMap B C) x := by
    rw [← graphCoordinatePermutation_symm]
    apply (graphCoordinatePermutation C rho).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (graphCoordinatePermutation_map (algebraMap B C) rho x).symm
  have hYback : graphCoordinatePermutation C rho.symm yC = graphCoefficientMap (algebraMap B C) y := by
    rw [← graphCoordinatePermutation_symm]
    apply (graphCoordinatePermutation C rho).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (graphCoordinatePermutation_map (algebraMap B C) rho y).symm
  rw [hXback, hYback]

end PfaffianDescent.Coray
