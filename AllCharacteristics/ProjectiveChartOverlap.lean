import AllCharacteristics.GradedChartOverlap
import AllCharacteristics.ProjectivePointCoordinates

/-!
# Actual intersections of projective coordinate charts

The product-coordinate chart is the actual pullback of two standard affine
charts. Its ring maps preserve the coefficient base and obey the normalized
coordinate transition rule with a constructed unit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The homogeneous ring of the intersection of the j-th and l-th coordinate charts. -/
abbrev ChartOverlapRing (j l : σ) :=
  Away (grading I) (coordinate I j * coordinate I l)

/-- Restrict the j-th chart to the product-coordinate intersection. -/
noncomputable def chartOverlapLeftMap (j l : σ) : ChartRing I j →+* ChartOverlapRing I j l :=
  awayMap (grading I) (coordinate_mem I l) rfl

/-- Restrict the l-th chart to the same product-coordinate intersection. -/
noncomputable def chartOverlapRightMap (j l : σ) : ChartRing I l →+* ChartOverlapRing I j l :=
  awayMap (grading I) (coordinate_mem I j) (mul_comm _ _)

/-- The left restriction preserves base coefficients. -/
theorem chartOverlapLeftMap_baseMap (j l : σ) (r : R) :
    chartOverlapLeftMap I j l (chartBaseMap I j r) =
      GradedChart.baseMap (grading I) (z := coordinate I j * coordinate I l) r :=
  GradedChart.awayMap_baseMap (grading I) (coordinate_mem I l) rfl r

/-- The right restriction preserves the same base coefficients. -/
theorem chartOverlapRightMap_baseMap (j l : σ) (r : R) :
    chartOverlapRightMap I j l (chartBaseMap I l r) =
      GradedChart.baseMap (grading I) (z := coordinate I j * coordinate I l) r :=
  GradedChart.awayMap_baseMap (grading I) (coordinate_mem I j) (mul_comm _ _) r

/-- The ratio of the j-th to the l-th coordinate is an actual unit on the overlap. -/
noncomputable def chartOverlapUnit (j l : σ) : (ChartOverlapRing I j l)ˣ :=
  GradedChart.overlapCoordinateUnit (grading I) (coordinate_mem I j) (coordinate_mem I l)

/-- The overlap unit is the image of the new distinguished coefficient. -/
theorem chartOverlapUnit_val (j l : σ) :
    (chartOverlapUnit I j l : ChartOverlapRing I j l) =
      chartOverlapRightMap I j l (chartCoordinate I l j) := rfl

/-- The inverse overlap unit is the oppositely normalized coordinate. -/
theorem chartOverlapUnit_inv (j l : σ) :
    (↑((chartOverlapUnit I j l)⁻¹) : ChartOverlapRing I j l) =
      chartOverlapLeftMap I j l (chartCoordinate I j l) := rfl

/-- The actual restriction maps satisfy the normalized-coordinate transition rule. -/
theorem chartOverlap_coordinate_relation (j l m : σ) :
    chartOverlapLeftMap I j l (chartCoordinate I j m) =
      (↑((chartOverlapUnit I j l)⁻¹) : ChartOverlapRing I j l) *
        chartOverlapRightMap I j l (chartCoordinate I l m) :=
  (GradedChart.normalized_overlap_mul (grading I) (coordinate_mem I j)
    (coordinate_mem I l) (coordinate I m) (coordinate_mem I m)).symm

/-- The intersection of the two actual affine coordinate charts is the spectrum
of the product-coordinate homogeneous localization. -/
noncomputable def chartOverlapIso (j l : σ) :
    pullback (chartι I j) (chartι I l) ≅ Spec (.of (ChartOverlapRing I j l)) :=
  Proj.pullbackAwayιIso (grading I) (coordinate_mem I j) (by decide : 0 < 1)
    (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The intersection identification respects its left projection. -/
theorem chartOverlapIso_hom_fst (j l : σ) :
    (chartOverlapIso I j l).hom ≫ Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j l)) =
      pullback.fst (chartι I j) (chartι I l) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left (grading I) (coordinate_mem I j)
    (by decide : 0 < 1) (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The intersection identification respects its right projection. -/
theorem chartOverlapIso_hom_snd (j l : σ) :
    (chartOverlapIso I j l).hom ≫ Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j l)) =
      pullback.snd (chartι I j) (chartι I l) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right (grading I) (coordinate_mem I j)
    (by decide : 0 < 1) (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The inverse intersection identification has the specified left restriction map. -/
theorem chartOverlapIso_inv_fst (j l : σ) :
    (chartOverlapIso I j l).inv ≫ pullback.fst (chartι I j) (chartι I l) =
      Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j l)) :=
  Proj.pullbackAwayιIso_inv_fst (grading I) (coordinate_mem I j)
    (by decide : 0 < 1) (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The inverse intersection identification has the specified right restriction map. -/
theorem chartOverlapIso_inv_snd (j l : σ) :
    (chartOverlapIso I j l).inv ≫ pullback.snd (chartι I j) (chartι I l) =
      Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j l)) :=
  Proj.pullbackAwayιIso_inv_snd (grading I) (coordinate_mem I j)
    (by decide : 0 < 1) (coordinate_mem I l) (by decide : 0 < 1) rfl

/-- The explicit overlap restrictions form an actual Cartesian square. -/
theorem isPullback_chartOverlap (j l : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j l)))
      (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j l))) (chartι I j) (chartι I l) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (chartOverlapIso I j l).symm
    (chartOverlapIso_inv_fst I j l) (chartOverlapIso_inv_snd I j l)
  rw [← chartOverlapIso_inv_fst, ← chartOverlapIso_inv_snd, Category.assoc,
    Category.assoc, pullback.condition]

/-- The left overlap projection is an actual open immersion. -/
instance isOpenImmersion_chartOverlapLeftMap (j l : σ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j l))) := by
  have h : IsOpenImmersion ((chartOverlapIso I j l).inv ≫
      pullback.fst (chartι I j) (chartι I l)) := inferInstance
  exact (chartOverlapIso_inv_fst I j l) ▸ h

/-- The right overlap projection is an actual open immersion. -/
instance isOpenImmersion_chartOverlapRightMap (j l : σ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j l))) := by
  have h : IsOpenImmersion ((chartOverlapIso I j l).inv ≫
      pullback.snd (chartι I j) (chartι I l)) := inferInstance
  exact (chartOverlapIso_inv_snd I j l) ▸ h

end HomogeneousProjective
end AllCharacteristics
