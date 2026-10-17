import PfaffianDescent.ActualLinearFrameNormalizedPointSquare
import PfaffianDescent.ActualCrossChartFrameBasisComparison
import PfaffianDescent.CoordinateVertexLengthTwoActualTangent

/-! SOURCE ONLY, UNVERIFIED. Derive normalized column maps from the ACTUAL
ambient coordinate frame; then derive its diagonal/permutation comparison.
The support-map equality is the legitimate meaning of the supplied frame
placing those actual points at vertices, not a matrix-comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateVertexMap_toAmbient_actual_normalized_point (i : Fin 4) :
    coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥ =
      ambientNormalizedCoordinateChartPoint (F := K) (coordinateVertexCoordinates i) i
        (by simp [coordinateVertexCoordinates]) := by
  have hb : (coordinateVertexChartHom (K := K) i).comp (chartBaseMap ⊥ i) =
      algebraMap K K := by
    apply RingHom.ext
    intro c
    exact normalizedPointChartMap_base ⊥ (coordinateVertexCoordinates i) i
      (by simp [coordinateVertexCoordinates]) (by intro p hp; simp [Ideal.mem_bot.mp hp]) c
  have hx : (fun s => coordinateVertexChartHom (K := K) i (chartCoordinate ⊥ i s)) =
      coordinateVertexCoordinates i := by
    funext s
    exact normalizedPointChartMap_coordinate ⊥ (coordinateVertexCoordinates i) i
      (by simp [coordinateVertexCoordinates]) (by intro p hp; simp [Ideal.mem_bot.mp hp]) s
  have h := ambientNormalizedCoordinateChartPoint_eq_original_chart (k := K) ⊥ i
    (coordinateVertexChartHom i) hb
  have hPointCongr (a b : Fin 4 → K) (s : Fin 4) (ha : a s = 1) (hb : b s = 1)
      (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a s ha =
        ambientNormalizedCoordinateChartPoint (F := K) b s hb := by
    subst b
    rfl
  exact h.symm.trans (hPointCongr _ _ i _ _ hx)

/-- This proves the point square from the literal ambient GL map. It has no
support-map or column-proportionality comparison hypothesis. -/
theorem actual_frame_vertex_column_square
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (i r : Fin 4) (hr : M r i ≠ 0) :
    (coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) ≫
      (linearCoordinateChangeAmbientIso M hM).inv =
    ambientNormalizedCoordinateChartPoint (F := K)
      (fun s => M s i / M r i) r (by exact div_self hr) := by
  let v : Fin 4 → K := coordinateVertexCoordinates i
  let x : Fin 4 → K := fun s => (M r i)⁻¹ * v s
  let y := (M.map (algebraMap K K)).mulVec x
  have hy (s : Fin 4) : y s = M s i / M r i := by
    simp [y, x, v, coordinateVertexCoordinates, Matrix.mulVec, dotProduct,
      Finset.sum_ite_eq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hOne : y r = 1 := by rw [hy, div_self hr]
  let ell := linearCoordinate M r
  have hell : ell.IsHomogeneous 1 := linearCoordinate_homogeneous M r
  have hxell : ell.eval₂ (algebraMap K K) x = 1 := by
    change aeval (R := K) x (linearCoordinate M r) = 1
    rw [linearCoordinate_aeval]
    exact hOne
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K K) x = 0 := by
    intro p hp
    simp [show p = 0 from Ideal.mem_bot.mp hp]
  let u : Kˣ := Units.mk0 (M r i)⁻¹ (inv_ne_zero hr)
  have hui : (u : K) = x i := by simp [u, x, v, coordinateVertexCoordinates]
  have hCoords : (fun s => (↑(u⁻¹) : K) * x s) = v := by
    funext s
    simp [u, x, Units.val_inv_eq_inv_val, ← mul_assoc, hr]
  have hPointCongr (a b : Fin 4 → K) (s : Fin 4) (ha : a s = 1) (hb : b s = 1)
      (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a s ha =
        ambientNormalizedCoordinateChartPoint (F := K) b s hb := by
    subst b
    rfl
  have hSource : linearNormalizedPoint ⊥ x ell hell hxell he ≫ quotientProjMap ⊥ =
      coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥ := by
    calc
      _ = ambientNormalizedCoordinateChartPoint (F := K)
          (fun s => (↑(u⁻¹) : K) * x s) i (by rw [← hui]; simp) :=
        linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint ⊥ x ell hell hxell he i u hui
      _ = ambientNormalizedCoordinateChartPoint v i (by simp [v, coordinateVertexCoordinates]) := by
        exact hPointCongr _ _ i _ _ hCoords
      _ = _ := (coordinateVertexMap_toAmbient_actual_normalized_point i).symm
  have hSquare := actual_linear_frame_normalized_point_square M hM x r hOne
  dsimp only at hSquare
  rw [hSource] at hSquare
  have hY : y = fun s => M s i / M r i := funext hy
  change ((coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) ≫
    (linearCoordinateChangeAmbientIso M hM).inv) =
      ambientNormalizedCoordinateChartPoint (F := K) y r hOne at hSquare
  exact hSquare.trans (hPointCongr _ _ r _ _ hY)

/-- Starting from the actual supplied-frame support square, derive the
column scalars and actual basis equality with no normalizer certificate. -/
theorem actual_supplied_ambient_frame_basis_comparison
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ i, b i j = 1) (rho : Equiv.Perm (Fin 4))
    (hFrame : ∀ i,
      (coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) ≫
        (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
          (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv =
      ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i))) :
    ∃ hNormalizer : ∀ i, supplied i j ≠ 0,
      supplied = QuarticNet.scaledRelabeledFrame b rho
        (fun i => Units.mk0 (supplied i j) (hNormalizer i)) := by
  apply actual_cross_chart_frame_basis_eq_scaled_relabel b supplied j hb rho
  intro i r hr
  have hs := actual_frame_vertex_column_square (QuarticNet.basisCoordinateMatrix supplied)
    (QuarticNet.basisCoordinateMatrix_isUnit supplied) i r hr
  exact hs.symm.trans (hFrame i)

end PfaffianDescent
