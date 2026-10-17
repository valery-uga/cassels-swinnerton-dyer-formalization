import PfaffianDescent.QuotientChartKernel
import PfaffianDescent.VoisinCubicSurfaceChartRegular

/-!
# Regular local equations for intersections on a smooth cubic surface

On each standard affine chart of a smooth cubic surface, adjoining a second
homogeneous cubic gives a principal quotient-chart kernel. If the second
cubic is regular modulo the surface equation, its normalized chart equation
is regular. This packages the local algebra needed for the effective Cartier
divisor of a moving cubic section.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restriction from a smooth cubic's affine chart to its intersection with
a second cubic's chart. -/
noncomputable def cubicIntersectionChartMap
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    ChartRing (equationIdeal a ha) j →+*
      ChartRing (equationIdeal a ha ⊔ equationIdeal p hp) j :=
  chartQuotientMap (equationIdeal a ha)
    (equationIdeal a ha ⊔ equationIdeal p hp)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j

/-- The second cubic is a regular principal equation on every chart of the
smooth first cubic, provided it is regular modulo the first equation. -/
theorem cubicIntersectionChartMap_ker_eq_regularEquation
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      p * x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) K)))
    (j : Fin 4) :
    RingHom.ker (cubicIntersectionChartMap a ha p hp j) =
      Ideal.span ({normalizedCubicSection a ha p hp j} :
        Set (ChartRing (equationIdeal a ha) j)) ∧
    IsRegular (normalizedCubicSection a ha p hp j) := by
  constructor
  · change RingHom.ker (chartQuotientMap (equationIdeal a ha)
        (equationIdeal a ha ⊔ equationIdeal p hp)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j) = _
    rw [chartQuotientMap_ker_eq_equation]
    exact congrArg (fun x : ChartRing (equationIdeal a ha) j =>
      Ideal.span ({x} : Set _))
        (by simpa only [normalizedCubicSection] using
          (eval₂_chartCoordinate_eq_fraction (equationIdeal a ha) j p hp))
  · exact normalizedCubicSection_isRegular a ha ha0 p hp hregular j

end PfaffianDescent
