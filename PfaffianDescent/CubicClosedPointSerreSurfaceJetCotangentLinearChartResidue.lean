import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalizationResidue

noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The exact degree-three homogeneous fraction q/ell³ has the original
jet derivative scaled by ell(x)^(-3). -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChart_fraction_derivative
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0)
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 3)
    (hqzero : aeval (fun j => (J j).fst) q = 0) :
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp ell hell J hunit hzero
      (Away.mk (grading (equationIdeal p hp))
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell) 3
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q)
        (by simpa using polynomial_class_mem_grading (equationIdeal p hp) q hq))).snd =
      (aeval (fun j => (J j).fst) ell)⁻¹ ^ 3 • (aeval J q).snd := by
  rw [← eval₂_linearChartCoordinate_eq_fraction (equationIdeal p hp)
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
    (polynomial_class_mem_grading (equationIdeal p hp) ell hell) q hq]
  unfold cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap
  rw [linearNormalizedPointChartMap_eval (equationIdeal p hp) _ ell hell]
  exact cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_derivative_scalar
    ell J hunit q hq hqzero

/-- The common-chart square-zero quotient has the literal original
projective point map as its residue map. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap_residue
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c x : Fin 4 → K)
    (hx : ∀ q ∈ (equationIdeal p hp).toIdeal, q.eval x = 0)
    (hcx : (homogeneousLinearForm c).eval x ≠ 0)
    (J : Fin 4 → CubicSurfaceFirstJet K) (hJ : ∀ j, (J j).fst = x j)
    (hunit : IsUnit (aeval J (homogeneousLinearForm c))) (hzero : aeval J p = 0) :
    (TrivSqZeroExt.fstHom K K (Fin 2 → K)).toRingHom.comp
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp
        (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
        J hunit hzero) =
      projectiveVectorSchemePointInLinearChartMap (equationIdeal p hp) c x hx hcx := by
  unfold projectiveVectorSchemePointInLinearChartMap
  apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
  · apply RingHom.ext
    intro r
    change (cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
      J hunit hzero (AllCharacteristics.GradedChart.baseMap
        (grading (equationIdeal p hp)) r)).fst = algebraMap K K r
    unfold cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap
    rw [linearNormalizedPointChartMap_base]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · intro j
    change (cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
      J hunit hzero _).fst = normalizedVectorInLinearChart c x j
    unfold cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap
    rw [linearNormalizedPointChartMap_coordinate (equationIdeal p hp) _
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c),
      cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_fst]
    have hxJ : (fun k => (J k).fst) = x := funext hJ
    rw [hxJ, hJ j]
    rfl

end PfaffianDescent
