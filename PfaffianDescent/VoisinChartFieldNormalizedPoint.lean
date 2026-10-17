import PfaffianDescent.LinearNormalizedProjectivePoint

/-! Reconstructing a normalized projective point from an affine Proj chart map. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A field-valued ring map from an affine Proj chart yields normalized
homogeneous coordinates satisfying the ideal; the resulting projective
point is exactly the original chart map followed by the chart immersion. -/
theorem chartFieldPoint_normalizedPointAt
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellz : Ideal.Quotient.mk I.toIdeal ell = z)
    (g : Away (grading I) z →+* F)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K F) :
    let x : Fin 4 → F := fun j => g (linearChartCoordinate I z hz j)
    ell.eval₂ (algebraMap K F) x = 1 ∧
    ∃ (he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0),
    ∃ (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) z = 1),
      linearNormalizedPointAt I x he z hz hzOne =
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (grading I) z hz (by decide : 0 < 1) := by
  classical
  dsimp only
  let x : Fin 4 → F := fun j => g (linearChartCoordinate I z hz j)
  have heval : eval₂Hom (algebraMap K F) x =
      g.comp (eval₂Hom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap K F) x = g (q.eval₂ _ _)
    rw [hom_eval₂, hbase]
  have hxell : ell.eval₂ (algebraMap K F) x = 1 := by
    change eval₂Hom (algebraMap K F) x ell = 1
    rw [heval, RingHom.comp_apply]
    change g (ell.eval₂
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz)) = 1
    rw [eval₂_linearChartCoordinate_eq_fraction I z hz ell hell]
    have hself := AllCharacteristics.GradedChart.normalized_self (grading I) hz
    change Away.mk (grading I) hz 1 z (by simpa only [one_smul] using hz) = 1 at hself
    have hfrac : Away.mk (grading I) hz 1 (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell) = 1 := by
      simpa only [hellz] using hself
    rw [hfrac, map_one]
  have he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K F) x = 0 := by
    intro q hq
    rw [← DirectSum.sum_support_decompose
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) q, MvPolynomial.eval₂_sum]
    apply Finset.sum_eq_zero
    intro n _
    let qn : MvPolynomial (Fin 4) K :=
      DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 4) K) q n
    have hqn : qn.IsHomogeneous n := by
      exact (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 4) K) q n).2
    have hqnI : qn ∈ I.toIdeal := I.isHomogeneous n hq
    change eval₂Hom (algebraMap K F) x qn = 0
    rw [heval, RingHom.comp_apply]
    rw [show eval₂Hom _ (linearChartCoordinate I z hz) qn = 0 from
      eval₂_linearChartCoordinate_eq_zero I z hz qn hqn hqnI, map_zero]
  have hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K F) x) he) z = 1 := by
    rw [← hellz]
    exact hxell
  have hg : g = linearNormalizedPointChartMapAt I x he z hz hzOne :=
    linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I x he z hz hzOne g hbase (fun _ => rfl)
  refine ⟨hxell, he, hzOne, ?_⟩
  change Spec.map (CommRingCat.ofHom
    (linearNormalizedPointChartMapAt I x he z hz hzOne)) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = _
  rw [← hg]

end PfaffianDescent
