import PfaffianDescent.ActualFrameVertexColumnSquare
import PfaffianDescent.ActualRationalProjectivePointFaithfulness
import PfaffianDescent.FiniteFourActualSupportRelabeling

/-! SOURCE ONLY, UNVERIFIED. Comparing the SAME actual geometric support
set derives the labeling permutation, common-chart column units and actual
frame equality. No canonical-extracted-matrix equality is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def actualVertexAmbientPoint (i : Fin 4) :
    Proj (homogeneousSubmodule (Fin 4) K) :=
  (coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) (IsLocalRing.closedPoint K)

theorem actualVertexAmbientPoint_injective :
    Function.Injective (actualVertexAmbientPoint (K := K)) := by
  intro i j h
  have hPoint : ambientNormalizedCoordinateChartPoint (F := K) (coordinateVertexCoordinates i)
      i (by simp [coordinateVertexCoordinates]) (IsLocalRing.closedPoint K) =
      ambientNormalizedCoordinateChartPoint (F := K) (coordinateVertexCoordinates j)
        j (by simp [coordinateVertexCoordinates]) (IsLocalRing.closedPoint K) := by
    have hi := coordinateVertexMap_toAmbient_actual_normalized_point (K := K) i
    have hj := coordinateVertexMap_toAmbient_actual_normalized_point (K := K) j
    simpa only [actualVertexAmbientPoint, hi, hj] using h
  have hMaps := actual_normalized_rational_projective_maps_eq_of_same_point
    (coordinateVertexCoordinates i) (coordinateVertexCoordinates j) i j
    (by simp [coordinateVertexCoordinates]) (by simp [coordinateVertexCoordinates]) hPoint
  have hNe := (actual_normalized_point_equal_cross_chart_coordinates
    (coordinateVertexCoordinates i) (coordinateVertexCoordinates j) i j
    (by simp [coordinateVertexCoordinates]) (by simp [coordinateVertexCoordinates]) hMaps).1
  by_contra hij
  simp [coordinateVertexCoordinates, hij] at hNe

/-- Same actual geometric support set is the literal support requirement for
an independently supplied coordinate frame. The permutation and column
rescalings are all derived conclusions. -/
theorem actual_supplied_frame_support_labeling_and_basis_comparison
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4) (hb : ∀ i, b i j = 1)
    (hSupport : Set.range (fun i =>
        (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
          (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
            (actualVertexAmbientPoint (K := K) i)) =
      Set.range (fun i => ambientNormalizedCoordinateChartPoint (F := K) (b i) j (hb i)
        (IsLocalRing.closedPoint K))) :
    ∃ (rho : Equiv.Perm (Fin 4)) (hNormalizer : ∀ i, supplied i j ≠ 0),
      supplied = QuarticNet.scaledRelabeledFrame b rho
        (fun i => Units.mk0 (supplied i j) (hNormalizer i)) := by
  let T := (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
    (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
  letI : IsOpenImmersion T := by dsimp only [T]; infer_instance
  let f : Fin 4 → Proj (homogeneousSubmodule (Fin 4) K) := fun i =>
    ambientNormalizedCoordinateChartPoint (F := K) (b i) j (hb i) (IsLocalRing.closedPoint K)
  let g : Fin 4 → Proj (homogeneousSubmodule (Fin 4) K) := fun i =>
    T (actualVertexAmbientPoint (K := K) i)
  have hf : Function.Injective f := by
    intro i r h
    apply b.injective
    exact actual_normalized_rational_point_coordinates_eq_of_same_point
      (b i) (b r) j (hb i) (hb r) h
  have hg : Function.Injective g :=
    T.isOpenEmbedding.injective.comp actualVertexAmbientPoint_injective
  obtain ⟨rho, hLabels⟩ := finiteFour_actual_support_relabeling f g hf hg hSupport
  have hFrame (i : Fin 4) :
      (coordinateVertexMap (K := K) i ≫ quotientProjMap ⊥) ≫ T =
      ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i)) := by
    obtain ⟨r, hr⟩ : ∃ r, supplied i r ≠ 0 := by
      by_contra h
      push_neg at h
      exact supplied.ne_zero i (funext h)
    have hs := actual_frame_vertex_column_square (QuarticNet.basisCoordinateMatrix supplied)
      (QuarticNet.basisCoordinateMatrix_isUnit supplied) i r hr
    have hPoint : ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => supplied i s / supplied i r) r (by exact div_self hr)
          (IsLocalRing.closedPoint K) =
        ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i))
          (IsLocalRing.closedPoint K) := by
      have hEval := congrArg (fun m : Spec (.of K) ⟶
          Proj (homogeneousSubmodule (Fin 4) K) => m (IsLocalRing.closedPoint K)) hs
      exact hEval.symm.trans (hLabels i)
    exact hs.trans (actual_normalized_rational_projective_maps_eq_of_same_point
      (fun s => supplied i s / supplied i r) (b (rho i)) r j
      (by exact div_self hr) (hb (rho i)) hPoint)
  obtain ⟨hNormalizer, hBasis⟩ := actual_supplied_ambient_frame_basis_comparison b supplied j hb rho hFrame
  exact ⟨rho, hNormalizer, hBasis⟩

end PfaffianDescent
