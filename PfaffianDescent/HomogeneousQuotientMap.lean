import PfaffianDescent.ProjectiveClosedImmersion
import PfaffianDescent.LinearChartCoordinates
import AllCharacteristics.HomogeneousProjective
import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.CoordinateCharts
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.GradedAwayMap

/-!
# Projective maps induced by homogeneous quotient ideals

An inclusion of homogeneous ideals gives a quotient of their homogeneous
coordinate rings.  This file packages the resulting graded surjection and
the corresponding closed immersion of projective schemes.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

section

variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
  (hIJ : I.toIdeal ≤ J.toIdeal)

/-- The quotient map between homogeneous coordinate rings induced by an
inclusion of homogeneous ideals. -/
noncomputable def coordinateQuotientMap : CoordinateRing I →+* CoordinateRing J :=
  Ideal.Quotient.factor hIJ

lemma coordinateQuotientMap_mk (a : MvPolynomial σ R) :
    coordinateQuotientMap I J hIJ (Ideal.Quotient.mk I.toIdeal a) =
      Ideal.Quotient.mk J.toIdeal a :=
  rfl

/-- The quotient map preserves the projective coordinate classes. -/
lemma coordinateQuotientMap_coordinate (j : σ) :
    coordinateQuotientMap I J hIJ (coordinate I j) = coordinate J j :=
  rfl

/-- The coordinate quotient preserves homogeneous degrees. -/
lemma coordinateQuotientMap_mem {n : ℕ} {x : CoordinateRing I}
    (hx : x ∈ grading I n) : coordinateQuotientMap I J hIJ x ∈ grading J n := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, (coordinateQuotientMap_mk I J hIJ a).symm⟩

/-- The coordinate quotient as a graded ring morphism. -/
noncomputable def gradedQuotientMap : grading I →+*ᵍ grading J where
  __ := coordinateQuotientMap I J hIJ
  map_mem hx := coordinateQuotientMap_mem I J hIJ hx

lemma gradedQuotientMap_surjective : Function.Surjective (gradedQuotientMap I J hIJ) :=
  Ideal.Quotient.factor_surjective hIJ

/-- The graded quotient preserves each projective coordinate. -/
lemma gradedQuotientMap_coordinate (j : σ) :
    gradedQuotientMap I J hIJ (coordinate I j) = coordinate J j :=
  coordinateQuotientMap_coordinate I J hIJ j

/-- The quotient map on the affine chart at a projective coordinate. -/
noncomputable def chartQuotientMap (j : σ) : ChartRing I j →+* ChartRing J j :=
  gradedAwayMapOfEq (gradedQuotientMap I J hIJ) (coordinate I j) (coordinate J j)
    (gradedQuotientMap_coordinate I J hIJ j)

/-- The quotient map on an arbitrary degree-one homogeneous chart.  This is
the chart form needed when a finite subscheme is normalized by a linear form
rather than by one of the coordinate variables. -/
noncomputable def awayQuotientMap (z : CoordinateRing I) (hz : z ∈ grading I 1) :
    Away (grading I) z →+* Away (grading J) (gradedQuotientMap I J hIJ z) :=
  gradedAwayMapOfEq (gradedQuotientMap I J hIJ) z
    (gradedQuotientMap I J hIJ z) rfl

/-- Arbitrary normalized projective coordinates commute with the homogeneous
quotient chart map. -/
lemma awayQuotientMap_linearChartCoordinate (z : CoordinateRing I)
    (hz : z ∈ grading I 1) (j : σ) :
    awayQuotientMap I J hIJ z hz (linearChartCoordinate I z hz j) =
      linearChartCoordinate J (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) j := by
  unfold awayQuotientMap linearChartCoordinate AllCharacteristics.GradedChart.normalized
  change (gradedAwayMapOfEq (gradedQuotientMap I J hIJ) z
    (gradedQuotientMap I J hIJ z) rfl)
      (Away.mk (grading I) hz 1 (coordinate I j)
        (by simpa only [one_smul] using coordinate_mem I j)) = _
  rw [AllCharacteristics.gradedAwayMapOfEq_mk
    (gradedQuotientMap I J hIJ) z (gradedQuotientMap I J hIJ z) rfl hz
    ((gradedQuotientMap I J hIJ).map_mem hz) 1 (coordinate I j) (coordinate_mem I j)]
  cases gradedQuotientMap_coordinate I J hIJ j
  rfl

/-- The arbitrary quotient chart map preserves coefficients. -/
lemma awayQuotientMap_baseMap (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (r : R) :
    awayQuotientMap I J hIJ z hz
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z) r) =
    AllCharacteristics.GradedChart.baseMap (grading J)
      (z := gradedQuotientMap I J hIJ z) r := by
  rfl

lemma chartQuotientMap_fromZero (j : σ) (a : grading I 0) :
    chartQuotientMap I J hIJ j
      (HomogeneousLocalization.fromZeroRingHom (grading I) (.powers (coordinate I j)) a) =
    HomogeneousLocalization.fromZeroRingHom (grading J) (.powers (coordinate J j))
      ⟨gradedQuotientMap I J hIJ a, (gradedQuotientMap I J hIJ).map_mem a.2⟩ := by
  rfl

lemma gradedQuotientMap_algebraMap_gradeZero (r : R) :
    gradedQuotientMap I J hIJ (algebraMap R (grading I 0) r) =
      algebraMap R (grading J 0) r := by
  change coordinateQuotientMap I J hIJ
      (Ideal.Quotient.mk I.toIdeal (MvPolynomial.C r)) =
    Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r)
  rfl

lemma chartQuotientMap_chartBaseMap (j : σ) :
    (chartQuotientMap I J hIJ j).comp (chartBaseMap I j) = chartBaseMap J j := by
  apply RingHom.ext
  intro r
  change (chartQuotientMap I J hIJ j)
      (HomogeneousLocalization.fromZeroRingHom (grading I) _
        (algebraMap R (grading I 0) r)) = _
  rw [chartQuotientMap_fromZero]
  change HomogeneousLocalization.fromZeroRingHom (grading J) (.powers (coordinate J j))
      ⟨gradedQuotientMap I J hIJ (algebraMap R (grading I 0) r),
        (gradedQuotientMap I J hIJ).map_mem (algebraMap R (grading I 0) r).2⟩ =
    HomogeneousLocalization.fromZeroRingHom (grading J) (.powers (coordinate J j))
      (algebraMap R (grading J 0) r)
  congr 1

/- The quotient chart map preserves the normalized projective coordinates. -/
lemma chartQuotientMap_chartCoordinate (j i : σ) :
    chartQuotientMap I J hIJ j (chartCoordinate I j i) =
      chartCoordinate J j i := by
  unfold chartQuotientMap chartCoordinate AllCharacteristics.GradedChart.normalized
  change (gradedAwayMapOfEq (gradedQuotientMap I J hIJ)
      (coordinate I j) (coordinate J j)
      (gradedQuotientMap_coordinate I J hIJ j))
      (HomogeneousLocalization.Away.mk (grading I) (coordinate_mem I j) 1
        (coordinate I i) (by simpa only [one_smul] using coordinate_mem I i)) = _
  rw [gradedAwayMapOfEq_mk (gradedQuotientMap I J hIJ) (coordinate I j)
    (coordinate J j) (gradedQuotientMap_coordinate I J hIJ j)
    (coordinate_mem I j) (coordinate_mem J j) 1 (coordinate I i)
    (coordinate_mem I i)]
  cases gradedQuotientMap_coordinate I J hIJ i
  rfl

/- Consequently, evaluation of any polynomial commutes with passage to the
   quotient chart.  This is the evaluation form used by the Jacobian bridge. -/
lemma chartQuotientMap_eval₂ (j : σ) (p : MvPolynomial σ R) :
    chartQuotientMap I J hIJ j
      (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      p.eval₂ (chartBaseMap J j) (chartCoordinate J j) := by
  rw [MvPolynomial.eval₂_comp_left]
  rw [chartQuotientMap_chartBaseMap]
  congr 1

/-- Every element of a quotient projective chart lifts from the original
chart. -/
theorem chartQuotientMap_surjective (j : σ) :
    Function.Surjective (chartQuotientMap I J hIJ j) := by
  intro x
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective J j x
  exact ⟨p.eval₂ (chartBaseMap I j) (chartCoordinate I j),
    chartQuotientMap_eval₂ I J hIJ j p⟩

/-- Quotienting homogeneous projective charts in two stages agrees with
quotienting directly. -/
theorem chartQuotientMap_comp
    (K : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (hJK : J.toIdeal ≤ K.toIdeal) (hIK : I.toIdeal ≤ K.toIdeal) (j : σ) :
    (chartQuotientMap J K hJK j).comp (chartQuotientMap I J hIJ j) =
      chartQuotientMap I K hIK j := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
  change (chartQuotientMap J K hJK j)
      ((chartQuotientMap I J hIJ j)
        (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))) =
    (chartQuotientMap I K hIK j)
      (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))
  rw [chartQuotientMap_eval₂ I J hIJ j p,
    chartQuotientMap_eval₂ J K hJK j p,
    chartQuotientMap_eval₂ I K hIK j p]

/-- The projective morphism from the larger homogeneous zero locus to the
smaller one. -/
noncomputable def schemeQuotientMap : scheme J ⟶ scheme I :=
  Proj.map (gradedQuotientMap I J hIJ)
    (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
      (gradedQuotientMap_surjective I J hIJ))

/-- The quotient immersion agrees with `awayQuotientMap` on every
degree-one homogeneous chart, including charts selected by finite-subscheme
avoidance. -/
theorem awayι_schemeQuotientMap (z : CoordinateRing I) (hz : z ∈ grading I 1) :
    Proj.awayι (grading J) (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) (by decide : 0 < 1) ≫
      schemeQuotientMap I J hIJ =
    Spec.map (CommRingCat.ofHom (awayQuotientMap I J hIJ z hz)) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
  change Proj.awayι (grading J) (gradedQuotientMap I J hIJ z)
      ((gradedQuotientMap I J hIJ).map_mem hz) (by decide : 0 < 1) ≫
    Proj.map (gradedQuotientMap I J hIJ)
      (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
        (gradedQuotientMap_surjective I J hIJ)) = _
  exact AllCharacteristics.awayι_comp_map_of_eq
    (gradedQuotientMap I J hIJ)
    (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
      (gradedQuotientMap_surjective I J hIJ))
    z (gradedQuotientMap I J hIJ z) rfl (by decide : 0 < 1) hz
    ((gradedQuotientMap I J hIJ).map_mem hz)

/-- On each coordinate chart, the quotient immersion is the localized quotient
of the homogeneous coordinate rings. -/
theorem chartι_schemeQuotientMap (j : σ) :
    chartι J j ≫ schemeQuotientMap I J hIJ =
      Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)) ≫ chartι I j := by
  have hm := awayι_comp_map_of_eq (gradedQuotientMap I J hIJ)
    (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
      (gradedQuotientMap_surjective I J hIJ))
    (coordinate I j) (coordinate J j) (gradedQuotientMap_coordinate I J hIJ j)
    (by decide : 0 < 1) (coordinate_mem I j) (coordinate_mem J j)
  change chartι J j ≫ schemeQuotientMap I J hIJ =
    Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)) ≫ chartι I j at hm
  exact hm

/-- The inverse image of a standard coordinate chart under a homogeneous
quotient morphism is the corresponding chart of the quotient scheme. -/
theorem schemeQuotientMap_preimage_chart (j : σ) :
    schemeQuotientMap I J hIJ ⁻¹ᵁ (chartι I j).opensRange =
      (chartι J j).opensRange := by
  rw [chartι_opensRange, chartι_opensRange]
  change Proj.map (gradedQuotientMap I J hIJ)
    (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
      (gradedQuotientMap_surjective I J hIJ)) ⁻¹ᵁ
        Proj.basicOpen (grading I) (coordinate I j) =
          Proj.basicOpen (grading J) (coordinate J j)
  rw [Proj.map_preimage_basicOpen, gradedQuotientMap_coordinate]

/-- The quotient's affine coordinate chart is exactly the inverse image
of the original scheme's coordinate chart. -/
theorem isPullback_schemeQuotientMap_chart (j : σ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)))
      (chartι J j) (chartι I j) (schemeQuotientMap I J hIJ) :=
  IsOpenImmersion.isPullback _ _ _ _
    (chartι_schemeQuotientMap I J hIJ j)
    (schemeQuotientMap_preimage_chart I J hIJ j)

/-- A homogeneous quotient is a closed projective immersion. -/
theorem schemeQuotientMap_closedImmersion :
    IsClosedImmersion (schemeQuotientMap I J hIJ) := by
  exact projectiveMap_closedImmersion_of_surjective
    (gradedQuotientMap I J hIJ) (gradedQuotientMap_surjective I J hIJ)

/-- Passing first to an intermediate homogeneous quotient and then to the
ambient projective space is the canonical ambient map of the larger
quotient. -/
theorem schemeQuotientMap_comp_quotientProjMap :
    schemeQuotientMap I J hIJ ≫ quotientProjMap I = quotientProjMap J := by
  unfold schemeQuotientMap quotientProjMap
  let F := quotientGradedRingHom I
  let G := gradedQuotientMap I J hIJ
  have hGF : G.comp F = quotientGradedRingHom J := by
    ext x
    rfl
  have hcomp := Proj.map_comp F G
    (irrelevant_le_map_quotientGradedRingHom I)
    (gradedSurjective_irrelevant_le G
      (gradedQuotientMap_surjective I J hIJ))
  calc
    _ = Proj.map G (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective I J hIJ)) ≫
        Proj.map F (irrelevant_le_map_quotientGradedRingHom I) := by rfl
    _ = Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp
        (irrelevant_le_map_quotientGradedRingHom I)
        (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective I J hIJ))) := hcomp.symm
    _ = _ := by cases hGF; rfl

/-- Projective homogeneous quotient morphisms compose as the underlying
graded quotient maps do. -/
theorem schemeQuotientMap_comp
    (K : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (hJK : J.toIdeal ≤ K.toIdeal) (hIK : I.toIdeal ≤ K.toIdeal) :
    schemeQuotientMap J K hJK ≫ schemeQuotientMap I J hIJ =
      schemeQuotientMap I K hIK := by
  unfold schemeQuotientMap
  let F := gradedQuotientMap I J hIJ
  let G := gradedQuotientMap J K hJK
  have hGF : G.comp F = gradedQuotientMap I K hIK := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hcomp := Proj.map_comp F G
    (gradedSurjective_irrelevant_le F
      (gradedQuotientMap_surjective I J hIJ))
    (gradedSurjective_irrelevant_le G
      (gradedQuotientMap_surjective J K hJK))
  calc
    _ = Proj.map G (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective J K hJK)) ≫
        Proj.map F (gradedSurjective_irrelevant_le F
          (gradedQuotientMap_surjective I J hIJ)) := by rfl
    _ = Proj.map (G.comp F) (HomogeneousIdeal.irrelevant_le_map_comp
        (gradedSurjective_irrelevant_le F
          (gradedQuotientMap_surjective I J hIJ))
        (gradedSurjective_irrelevant_le G
          (gradedQuotientMap_surjective J K hJK))) := hcomp.symm
    _ = _ := by simp only [hGF]

/-- A homogeneous quotient immersion is a morphism over the original
coefficient ring. -/
theorem schemeQuotientMap_toBase :
    schemeQuotientMap I J hIJ ≫ toBase I = toBase J := by
  apply (coordinateOpenCover J).openCover.hom_ext
  intro j
  change σ at j
  change chartι J j ≫ (schemeQuotientMap I J hIJ ≫ toBase I) =
    chartι J j ≫ toBase J
  rw [← Category.assoc, chartι_schemeQuotientMap, Category.assoc,
    chartι_toBase, chartι_toBase, ← Spec.map_comp]
  apply congrArg Spec.map
  change CommRingCat.ofHom ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)) =
    CommRingCat.ofHom (chartBaseMap J j)
  rw [chartQuotientMap_chartBaseMap]

end

end PfaffianDescent
