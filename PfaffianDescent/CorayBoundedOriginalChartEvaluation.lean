import PfaffianDescent.CorayGradedChartSectionEvaluation
import PfaffianDescent.CorayBoundedOriginalSectionFamily
import PfaffianDescent.CoraySmoothCurveHilbert

/-! Source-only / unverified. The chart evaluation is on the actual
degree-n quotient family through the original residue coordinates.
It keeps n, K, and the chart coordinate; it does not choose a transverse
auxiliary line or assert that the rational image has dimension two. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped PfaffianDescent.Coray

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]

/-- Every ambient coordinate survives the quotient by a nonzero cubic.
There are no degree-one cubic relations. -/
theorem cubicCoordinate_ne_zero (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) (j : Fin 4) :
    coordinate (equationIdeal p hp) j ≠ 0 := by
  let x : PfaffianDescent.CubicSurfaceHomogeneous K 1 :=
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
  intro h
  have hx : x = 0 :=
    PfaffianDescent.cubicSurfaceProjection_injective_of_lt_three p hp hp0 1
      (by decide) (by
        change coordinate (equationIdeal p hp) j =
          PfaffianDescent.cubicSurfaceProjection p hp 1 0
        simpa only [map_zero] using h)
  exact MvPolynomial.X_ne_zero j (congrArg Subtype.val hx)

/-- Smoothness supplies the prime actual cone, so chart normalization
is injective in every prescribed degree. -/
theorem cubicGradeChartEvaluation_injective (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (j : Fin 4) :
    Function.Injective (gradedChartSectionEvaluation (grading (equationIdeal p hp))
      (coordinate_mem (equationIdeal p hp) j) n) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mpr
    exact PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  exact gradedChartSectionEvaluation_injective _ _
    (cubicCoordinate_ne_zero p hp hp0 j) n

/-- The exact bounded through-P family, with its existing K action,
evaluated as degree-n chart functions. -/
def cubicThroughPointChartEvaluation (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4) :
    cubicThroughCoordinateSections p hp n y hpy →ₗ[K]
      ChartRing (equationIdeal p hp) j :=
  (gradedChartSectionEvaluation (grading (equationIdeal p hp))
    (coordinate_mem (equationIdeal p hp) j) n).domRestrict _

theorem cubicThroughPointChartEvaluation_injective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4) :
    Function.Injective (cubicThroughPointChartEvaluation p hp n y hpy j) := by
  intro s t h
  apply Subtype.ext
  exact cubicGradeChartEvaluation_injective p hp hp0 n j h

/-- An actual basis of the bounded family gives nonzero projective
coordinates in every chart, without selecting an auxiliary point. -/
theorem cubicThroughPointChartBasis_ne_zero {m : ℕ} (hm : 0 < m)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) :
    (fun i => cubicThroughPointChartEvaluation p hp n y hpy j (b i)) ≠ 0 := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact evaluatedBasis_ne_zero
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := ChartRing (equationIdeal p hp) j) (ι := Fin m)
    b (cubicThroughPointChartEvaluation p hp n y hpy j)
    (cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j)

/-- Exact original-K nondegeneracy of these chart coordinates. This is
not an assertion of surface image dimension or tangent rank. -/
theorem cubicThroughPointChartBasis_relation_iff {m : ℕ}
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (c : Fin m → K) :
    (∑ i, c i • cubicThroughPointChartEvaluation p hp n y hpy j (b i) = 0) ↔ c = 0 := by
  exact evaluatedBasis_relation_iff
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (B := ChartRing (equationIdeal p hp) j) (ι := Fin m)
    b (cubicThroughPointChartEvaluation p hp n y hpy j)
    (cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j) c

end
end PfaffianDescent.Coray
end
