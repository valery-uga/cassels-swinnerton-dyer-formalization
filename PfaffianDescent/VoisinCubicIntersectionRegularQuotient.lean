import PfaffianDescent.VoisinFieldPointIntersectionChart
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual cubic-intersection charts as regular principal quotients

The checked chart kernel and surjectivity results identify each chart of
the two-cubic projective scheme with the quotient of the fixed smooth
cubic's chart by the normalized moving cubic. The quotient equation is
regular under the field-point regularity hypothesis.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {S : Type u} [Field S]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical map from the quotient by the normalized moving cubic
to the actual affine chart of the two-cubic projective intersection. -/
noncomputable def cubicIntersectionChartRegularQuotientEquiv
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hcharts : CubicIntersectionRegularOnCharts a ha p hp)
    (j : Fin 4) :
    (ChartRing (equationIdeal a ha) j ⧸
      Ideal.span ({normalizedCubicSection a ha p hp j} :
        Set (ChartRing (equationIdeal a ha) j))) ≃+*
      ChartRing (equationIdeal a ha ⊔ equationIdeal p hp) j := by
  let f := cubicIntersectionChartMap a ha p hp j
  have hker := (hcharts j).1
  have hsurj : Function.Surjective f := by
    exact chartQuotientMap_surjective _ _ _ j
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

theorem cubicIntersectionChartRegularQuotientEquiv_mk
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hcharts : CubicIntersectionRegularOnCharts a ha p hp)
    (j : Fin 4) (x : ChartRing (equationIdeal a ha) j) :
    cubicIntersectionChartRegularQuotientEquiv a ha p hp hcharts j
      (Ideal.Quotient.mk
        (Ideal.span ({normalizedCubicSection a ha p hp j} :
          Set (ChartRing (equationIdeal a ha) j))) x) =
        cubicIntersectionChartMap a ha p hp j x := by
  simp only [cubicIntersectionChartRegularQuotientEquiv,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

theorem cubicIntersectionChartRegularQuotientEquiv_equation_regular
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hcharts : CubicIntersectionRegularOnCharts a ha p hp)
    (j : Fin 4) :
    IsRegular (normalizedCubicSection a ha p hp j) :=
  (hcharts j).2

/-- Multiplication by the moving cubic is injective on every actual
chart of the fixed smooth cubic. -/
theorem cubicIntersectionChart_mulLeft_injective
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hcharts : CubicIntersectionRegularOnCharts a ha p hp)
    (j : Fin 4) :
    Function.Injective (fun x : ChartRing (equationIdeal a ha) j =>
      normalizedCubicSection a ha p hp j * x) :=
  (hcharts j).2.left

/-- The kernel of the actual chart restriction map is exactly the image
of multiplication by the moving cubic. -/
theorem cubicIntersectionChart_exact_at_surface
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (hcharts : CubicIntersectionRegularOnCharts a ha p hp)
    (j : Fin 4) (y : ChartRing (equationIdeal a ha) j) :
    cubicIntersectionChartMap a ha p hp j y = 0 ↔
      ∃ x, normalizedCubicSection a ha p hp j * x = y := by
  change y ∈ RingHom.ker (cubicIntersectionChartMap a ha p hp j) ↔ _
  rw [(hcharts j).1, Ideal.mem_span_singleton, dvd_def]
  exact exists_congr fun _ => eq_comm

end PfaffianDescent
