import PfaffianDescent.CubicElevenPointKernelScalarExtension
import PfaffianDescent.LinearChartCoordinates
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalization

/-! Literal cubic restriction to an actual field-valued homogeneous chart,
and its compatibility with the component algebra maps. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def cubicHomogeneousChartRestriction
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* L) : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] L :=
  (aeval (fun j => g (linearChartCoordinate I z hz j))).toLinearMap.domRestrict _

theorem cubicHomogeneousChartRestriction_fraction
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap F L) (q : homogeneousSubmodule (Fin 4) F 3) :
    g (Away.mk (grading I) hz 3 (Ideal.Quotient.mk I.toIdeal q.1)
      (by simpa using polynomial_class_mem_grading I q.1 q.2)) =
        cubicHomogeneousChartRestriction I z hz g q := by
  rw [← eval₂_linearChartCoordinate_eq_fraction I z hz q.1 q.2, hom_eval₂, hbase]
  rfl

theorem cubicHomogeneousChartRestriction_component
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* L) (α : L →ₐ[F] E)
    (q : homogeneousSubmodule (Fin 4) F 3) :
    aeval (fun j => α (g (linearChartCoordinate I z hz j)))
        (q.1.map (algebraMap F E)) =
      α (cubicHomogeneousChartRestriction I z hz g q) := by
  have hα : α.toRingHom.comp (algebraMap F L) = algebraMap F E :=
    RingHom.ext α.commutes
  change eval (fun j => α (g (linearChartCoordinate I z hz j)))
    (q.1.map (algebraMap F E)) =
      α (eval₂ (algebraMap F L) (fun j => g (linearChartCoordinate I z hz j)) q.1)
  rw [eval_map]
  have h := hom_eval₂ q.1 (algebraMap F L) α.toRingHom
    (fun j => g (linearChartCoordinate I z hz j))
  rw [hα] at h
  exact h.symm

theorem cubicHomogeneousChartRestriction_mem_elevenPointKernel
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* L) (α : Fin 11 → (L →ₐ[F] E))
    (x : Fin 11 → Fin 4 → E) (s : Fin 11 → E)
    (hcoords : ∀ k j, x k j = s k * α k (g (linearChartCoordinate I z hz j)))
    (q : homogeneousSubmodule (Fin 4) F 3)
    (hq : cubicHomogeneousChartRestriction I z hz g q = 0) :
    cubicElevenPointValueRestriction x
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0 := by
  funext k
  simp only [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
    finite_product_evaluation_apply, Pi.zero_apply]
  change aeval (x k) (q.1.map (algebraMap F E)) = 0
  rw [show x k = fun j => s k * α k (g (linearChartCoordinate I z hz j)) from
    funext (hcoords k)]
  rw [cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous
    _ (q.2.map (algebraMap F E)), cubicHomogeneousChartRestriction_component,
    hq, map_zero, mul_zero]

end PfaffianDescent
