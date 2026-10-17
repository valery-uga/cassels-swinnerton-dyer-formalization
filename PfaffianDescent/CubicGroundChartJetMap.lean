import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartResidue
import PfaffianDescent.CubicHomogeneousChartRestriction

/-! Literal square-zero jets on the ground-field cubic chart, with a
different geometric point field. The coefficient and coordinate maps are
retained for the actual ideal-fibre derivative comparison. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial TrivSqZeroExt HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

theorem cubicGroundChartJet_eval₂_map
    (x : Fin 4 → CubicSurfaceFirstJet E) (q : MvPolynomial (Fin 4) F) :
    q.eval₂ (algebraMap F (CubicSurfaceFirstJet E)) x =
      aeval x (q.map (algebraMap F E)) := by
  change _ = eval₂ (algebraMap E (CubicSurfaceFirstJet E)) x _
  rw [eval₂_map, ← IsScalarTower.algebraMap_eq F E (CubicSurfaceFirstJet E)]

def cubicGroundChartJet_coordinates (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j)) :
    Fin 4 → CubicSurfaceFirstJet E :=
  cubicClosedPointSerreSurfaceJetCotangent_normalizedJet (X j) J
    (by simpa only [aeval_X] using hunit)

theorem cubicGroundChartJet_coordinates_anchor (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j)) :
    cubicGroundChartJet_coordinates j J hunit j = 1 := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell
    (X j : MvPolynomial (Fin 4) E) J (isHomogeneous_X E j)
      (by simpa only [aeval_X] using hunit)
  simpa only [aeval_X, cubicGroundChartJet_coordinates] using h

theorem cubicGroundChartJet_coordinates_cubic
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0) :
    P.eval₂ (algebraMap F (CubicSurfaceFirstJet E))
      (cubicGroundChartJet_coordinates j J hunit) = 0 := by
  rw [cubicGroundChartJet_eval₂_map]
  exact cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_cubic
    (X j) J (by simpa only [aeval_X] using hunit)
      (P.map (algebraMap F E)) (hP.map (algebraMap F E)) hzero

def cubicGroundChartJetMap
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0) :
    ChartRing (equationIdeal P hP) j →+* CubicSurfaceFirstJet E := by
  let nJ := cubicGroundChartJet_coordinates j J hunit
  have he : ∀ q ∈ (equationIdeal P hP).toIdeal,
      q.eval₂ (algebraMap F (CubicSurfaceFirstJet E)) nJ = 0 := by
    intro q hq
    change q ∈ Ideal.span ({P} : Set (MvPolynomial (Fin 4) F)) at hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    rw [hr, eval₂_mul, cubicGroundChartJet_coordinates_cubic P hP j J hunit hzero, zero_mul]
  have hn : (X j : MvPolynomial (Fin 4) F).eval₂
      (algebraMap F (CubicSurfaceFirstJet E)) nJ = 1 := by
    simpa only [eval₂_X] using cubicGroundChartJet_coordinates_anchor j J hunit
  exact linearNormalizedPointChartMap (equationIdeal P hP) nJ (X j) hn he

theorem cubicGroundChartJetMap_base
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0) (r : F) :
    cubicGroundChartJetMap P hP j J hunit hzero (chartBaseMap (equationIdeal P hP) j r) =
      algebraMap F (CubicSurfaceFirstJet E) r := by
  dsimp only [cubicGroundChartJetMap]
  exact linearNormalizedPointChartMap_base _ _ _ _ _ r

theorem cubicGroundChartJetMap_coordinate
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0) (r : Fin 4) :
    cubicGroundChartJetMap P hP j J hunit hzero
      (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
        (coordinate_mem (equationIdeal P hP) j) r) =
      cubicGroundChartJet_coordinates j J hunit r := by
  dsimp only [cubicGroundChartJetMap]
  exact linearNormalizedPointChartMap_coordinate _ _ _ (isHomogeneous_X F j) _ _ r

theorem cubicGroundChartJetMap_coordinate_residue
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0) (r : Fin 4) :
    (cubicGroundChartJetMap P hP j J hunit hzero
      (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
        (coordinate_mem (equationIdeal P hP) j) r)).fst =
      (J j).fst⁻¹ * (J r).fst := by
  rw [cubicGroundChartJetMap_coordinate]
  simpa only [aeval_X, cubicGroundChartJet_coordinates] using
    cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_fst
      (X j : MvPolynomial (Fin 4) E) J
        (by simpa only [aeval_X] using hunit) r

theorem cubicGroundChartJetMap_homogeneous
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0)
    (q : MvPolynomial (Fin 4) F) {d : ℕ} (hq : q.IsHomogeneous d) :
    cubicGroundChartJetMap P hP j J hunit hzero
      (q.eval₂ (chartBaseMap (equationIdeal P hP) j)
        (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
          (coordinate_mem (equationIdeal P hP) j))) =
      (↑hunit.unit⁻¹ : CubicSurfaceFirstJet E) ^ d *
        aeval J (q.map (algebraMap F E)) := by
  rw [hom_eval₂]
  have hb : (cubicGroundChartJetMap P hP j J hunit hzero).comp
      (chartBaseMap (equationIdeal P hP) j) = algebraMap F (CubicSurfaceFirstJet E) :=
    RingHom.ext (cubicGroundChartJetMap_base P hP j J hunit hzero)
  have hc : (fun r => cubicGroundChartJetMap P hP j J hunit hzero
      (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
        (coordinate_mem (equationIdeal P hP) j) r)) =
      cubicGroundChartJet_coordinates j J hunit :=
    funext (cubicGroundChartJetMap_coordinate P hP j J hunit hzero)
  rw [hb, hc, cubicGroundChartJet_eval₂_map]
  let hu : IsUnit (aeval J (X j : MvPolynomial (Fin 4) E)) :=
    by simpa only [aeval_X] using hunit
  have huu : hu.unit = hunit.unit := by
    apply Units.ext
    rw [hu.unit_spec, hunit.unit_spec, aeval_X]
  have h := cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous
    (X j) J hu (q.map (algebraMap F E)) (hq.map (algebraMap F E))
  rw [huu] at h
  exact h

end PfaffianDescent
