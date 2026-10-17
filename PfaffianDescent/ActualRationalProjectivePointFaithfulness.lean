import PfaffianDescent.ActualFieldPointChartNormalizer
import PfaffianDescent.RationalAffineChartPointFaithfulness

/-! SOURCE ONLY, UNVERIFIED. Genuine K-rational projective morphisms are
compared from their actual support POINTS, without assuming morphism equality.
Coefficient compatibility is proved from the actual normalized chart maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_normalized_rational_point_coordinates_eq_of_same_point
    (x y : Fin 4 → K) (j : Fin 4) (hx : x j = 1) (hy : y j = 1)
    (hPoint : ambientNormalizedCoordinateChartPoint (F := K) x j hx
        (IsLocalRing.closedPoint K) =
      ambientNormalizedCoordinateChartPoint (F := K) y j hy
        (IsLocalRing.closedPoint K)) : x = y := by
  let chart := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
    (isHomogeneous_X K j) (by decide : 0 < 1)
  letI : IsOpenImmersion chart := by
    dsimp only [chart, Proj.awayι]
    infer_instance
  let f := ambientNormalizedCoordinateChartMap (F := K) x j hx
  let g := ambientNormalizedCoordinateChartMap (F := K) y j hy
  let c := AllCharacteristics.GradedChart.baseMap
    (homogeneousSubmodule (Fin 4) K) (z := X j)
  have hf : f.comp c = RingHom.id K := by
    apply RingHom.ext
    intro a
    exact ambientNormalizedCoordinateChartMap_base x j hx a
  have hg : g.comp c = RingHom.id K := by
    apply RingHom.ext
    intro a
    exact ambientNormalizedCoordinateChartMap_base y j hy a
  have hSpec : Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint K) =
      Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint K) := by
    apply chart.isOpenEmbedding.injective
    exact hPoint
  have hfg := fieldValueRingHom_eq_of_same_spec_point c f g hf hg hSpec
  funext r
  have hr := DFunLike.congr_fun hfg (ambientChartCoordinate (R := K) j r)
  exact (ambientNormalizedCoordinateChartMap_coordinate x j hx r).symm.trans
    (hr.trans (ambientNormalizedCoordinateChartMap_coordinate y j hy r))

/-- Source and target may be normalized in DIFFERENT charts. Actual equality
of the K-rational support points suffices for equality of their morphisms. -/
theorem actual_normalized_rational_projective_maps_eq_of_same_point
    (x y : Fin 4 → K) (r j : Fin 4) (hx : x r = 1) (hy : y j = 1)
    (hPoint : ambientNormalizedCoordinateChartPoint (F := K) x r hx
        (IsLocalRing.closedPoint K) =
      ambientNormalizedCoordinateChartPoint (F := K) y j hy
        (IsLocalRing.closedPoint K)) :
    ambientNormalizedCoordinateChartPoint (F := K) x r hx =
      ambientNormalizedCoordinateChartPoint (F := K) y j hy := by
  have hOpen : ambientNormalizedCoordinateChartPoint (F := K) x r hx
      (IsLocalRing.closedPoint K) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j) := by
    rw [hPoint, ← Proj.opensRange_awayι (homogeneousSubmodule (Fin 4) K) (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)]
    exact ⟨Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap y j hy))
      (IsLocalRing.closedPoint K), rfl⟩
  have hne := actual_normalized_field_point_coordinate_ne_zero_of_basicOpen x r hx j hOpen
  let u : Kˣ := Units.mk0 (x j) hne
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K K) x = 0 := by
    intro p hp
    simp [show p = 0 from Ideal.mem_bot.mp hp]
  have hxX : (X r : MvPolynomial (Fin 4) K).eval₂ (algebraMap K K) x = 1 := by
    simpa only [eval₂_X] using hx
  have hOld := linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ x r hx he
  have hNew := linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint ⊥ x (X r)
    (isHomogeneous_X K r) hxX he j u rfl
  have hNormalize : ambientNormalizedCoordinateChartPoint (F := K) x r hx =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => (x j)⁻¹ * x s) j (by simp [hne]) := by
    simpa only [u, Units.val_inv_eq_inv_val, Units.val_mk0] using hOld.symm.trans hNew
  have hNormalizedPoint : ambientNormalizedCoordinateChartPoint (F := K)
      (fun s => (x j)⁻¹ * x s) j (by simp [hne]) (IsLocalRing.closedPoint K) =
        ambientNormalizedCoordinateChartPoint (F := K) y j hy (IsLocalRing.closedPoint K) := by
    rw [← hNormalize]
    exact hPoint
  have hCoords := actual_normalized_rational_point_coordinates_eq_of_same_point
    (fun s => (x j)⁻¹ * x s) y j (by simp [hne]) hy hNormalizedPoint
  have hPointCongr (a b : Fin 4 → K) (ha : a j = 1) (hb : b j = 1)
      (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a j ha =
        ambientNormalizedCoordinateChartPoint (F := K) b j hb := by
    subst b
    rfl
  exact hNormalize.trans (hPointCongr _ _ _ _ hCoords)

end PfaffianDescent
