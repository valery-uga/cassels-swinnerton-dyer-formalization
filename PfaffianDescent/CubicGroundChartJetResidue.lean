import PfaffianDescent.CubicGroundChartJetMap

/-! The ground chart jet has the literal component residue map and the
correct derivative of a cubic homogeneous fraction. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial TrivSqZeroExt HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicLinearChart_ringHom_ext
    {F A : Type u} [Field F] [CommRing A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (f g : Away (grading I) z →+* A)
    (hb : f.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)))
    (hc : ∀ r, f (linearChartCoordinate I z hz r) = g (linearChartCoordinate I z hz r)) :
    f = g := by
  apply RingHom.ext
  intro a
  obtain ⟨q, hq⟩ := eval₂_linearChartCoordinate_surjective I z hz a
  rw [← hq]
  change f (q.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz)) =
    g (q.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz))
  rw [hom_eval₂, hom_eval₂, hb]
  congr 1
  funext r
  exact hc r

theorem cubicGroundChartJetMap_residue_comp
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0)
    (g : ChartRing (equationIdeal P hP) j →+* L)
    (hgb : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (α : L →ₐ[F] E)
    (hc : ∀ r, α (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
      (J j).fst⁻¹ * (J r).fst) :
    (TrivSqZeroExt.fstHom E E (Fin 2 → E)).toRingHom.comp
      (cubicGroundChartJetMap P hP j J hunit hzero) = α.toRingHom.comp g := by
  apply cubicLinearChart_ringHom_ext (equationIdeal P hP)
    (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j)
  · apply RingHom.ext
    intro r
    change (cubicGroundChartJetMap P hP j J hunit hzero
      (chartBaseMap (equationIdeal P hP) j r)).fst = α (g (chartBaseMap (equationIdeal P hP) j r))
    rw [cubicGroundChartJetMap_base]
    have hg := RingHom.congr_fun hgb r
    change g (chartBaseMap (equationIdeal P hP) j r) = algebraMap F L r at hg
    rw [hg, α.commutes]
    rfl
  · intro r
    change (cubicGroundChartJetMap P hP j J hunit hzero _).fst = α (g _)
    exact (cubicGroundChartJetMap_coordinate_residue P hP j J hunit hzero r).trans (hc r).symm

theorem cubicGroundChartJetMap_cubic_derivative
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (j : Fin 4)
    (J : Fin 4 → CubicSurfaceFirstJet E) (hunit : IsUnit (J j))
    (hzero : aeval J (P.map (algebraMap F E)) = 0)
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3)
    (hqzero : aeval (fun r => (J r).fst) (q.map (algebraMap F E)) = 0) :
    (cubicGroundChartJetMap P hP j J hunit hzero
      (q.eval₂ (chartBaseMap (equationIdeal P hP) j)
        (linearChartCoordinate (equationIdeal P hP) (coordinate (equationIdeal P hP) j)
          (coordinate_mem (equationIdeal P hP) j)))).snd =
      (J j).fst⁻¹ ^ 3 • (aeval J (q.map (algebraMap F E))).snd := by
  rw [cubicGroundChartJetMap_homogeneous P hP j J hunit hzero q hq]
  let hu : IsUnit (aeval J (X j : MvPolynomial (Fin 4) E)) :=
    by simpa only [aeval_X] using hunit
  have huu : hu.unit = hunit.unit := by
    apply Units.ext
    rw [hu.unit_spec, hunit.unit_spec, aeval_X]
  have h := cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_derivative_scalar
    (X j : MvPolynomial (Fin 4) E) J hu
      (q.map (algebraMap F E)) (hq.map (algebraMap F E)) hqzero
  rw [cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous
    (X j) J hu (q.map (algebraMap F E)) (hq.map (algebraMap F E)), huu] at h
  simpa only [aeval_X] using h

end PfaffianDescent
