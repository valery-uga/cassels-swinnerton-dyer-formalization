import AllCharacteristics.HomogeneousProjective
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Coordinate affine charts of a projective polynomial quotient

The standard coordinate opens cover the actual projective scheme. Each chart
is the spectrum of the degree-zero localization at that coordinate, with its
explicit structure morphism to the coefficient ring.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The image of a homogeneous coordinate in the quotient ring. -/
noncomputable def coordinate (j : σ) : CoordinateRing (R := R) (σ := σ) I :=
  Ideal.Quotient.mk (I.toIdeal : Ideal (MvPolynomial σ R)) (MvPolynomial.X j : MvPolynomial σ R)

/-- Coordinates have degree one in the quotient grading. -/
theorem coordinate_mem (j : σ) : coordinate I j ∈ grading (R := R) (σ := σ) I 1 :=
  ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X R j, rfl⟩

/-- Every positive-degree homogeneous element belongs to the ideal generated
by the homogeneous coordinates. -/
theorem positive_degree_mem_coordinateIdeal {n : ℕ} (hn : 0 < n)
    {x : CoordinateRing (R := R) (σ := σ) I} (hx : x ∈ grading (R := R) (σ := σ) I n) :
    x ∈ Ideal.span (Set.range (coordinate I)) := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hpvars : p ∈ MvPolynomial.idealOfVars σ R := by
    rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm).symm
    exact he ▸ hn
  have hle : MvPolynomial.idealOfVars σ R ≤
      (Ideal.span (Set.range (coordinate I))).comap (Ideal.Quotient.mk I.toIdeal) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hle hpvars

/-- The homogeneous coordinates generate the irrelevant ideal. -/
theorem irrelevant_eq_coordinateIdeal :
    (HomogeneousIdeal.irrelevant (grading (R := R) (σ := σ) I)).toIdeal =
      Ideal.span (Set.range (coordinate I)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le (grading (R := R) (σ := σ) I)).mpr
    intro n hn x hx
    exact positive_degree_mem_coordinateIdeal I hn hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact HomogeneousIdeal.mem_irrelevant_of_mem (grading (R := R) (σ := σ) I) (by decide : 0 < 1)
      (coordinate_mem I j)

/-- The affine coordinate-chart ring. -/
abbrev ChartRing (j : σ) := Away (grading (R := R) (σ := σ) I) (coordinate I j)

/-- The standard coordinate chart as an open immersion into the projective
scheme. -/
noncomputable def chartι (j : σ) : Spec (.of (ChartRing I j)) ⟶ scheme (R := R) (σ := σ) I :=
  Proj.awayι (grading (R := R) (σ := σ) I) (coordinate I j) (coordinate_mem I j) (by decide : 0 < 1)

instance isOpenImmersion_chartι (j : σ) : IsOpenImmersion (chartι I j) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (grading (R := R) (σ := σ) I) (coordinate I j)
    (coordinate_mem I j) (by decide : 0 < 1)))

/-- The coordinate charts form an affine open cover. -/
noncomputable def coordinateOpenCover : (scheme (R := R) (σ := σ) I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading (R := R) (σ := σ) I) (coordinate I)
    (coordinate_mem I) (fun _ ↦ by decide : ∀ _ : σ, 0 < 1)
    (irrelevant_eq_coordinateIdeal I).le

/-- Every point lies in a coordinate chart. -/
theorem exists_coordinate_chart (x : scheme (R := R) (σ := σ) I) :
    ∃ j : σ, ∃ y : Spec (.of (ChartRing I j)), chartι I j y = x := by
  exact ⟨(coordinateOpenCover I).idx x, (coordinateOpenCover I).covers x⟩

/-- The coefficient map into a coordinate chart. -/
noncomputable def chartBaseMap (j : σ) : R →+* ChartRing I j :=
  (fromZeroRingHom (grading (R := R) (σ := σ) I) (.powers (coordinate I j))).comp
    (algebraMap R (grading (R := R) (σ := σ) I 0))

/-- The affine chart's coefficient map is compatible with the projective
scheme's structure morphism. -/
theorem chartι_toBase (j : σ) :
    chartι I j ≫ toBase I = Spec.map (CommRingCat.ofHom (chartBaseMap I j)) := by
  change Proj.awayι (grading I) (coordinate I j) (coordinate_mem I j)
      (by decide : 0 < 1) ≫ (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0)))) =
    Spec.map (CommRingCat.ofHom ((fromZeroRingHom (grading I) (.powers (coordinate I j))).comp
      (algebraMap R (grading I 0))))
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end HomogeneousProjective
end AllCharacteristics
