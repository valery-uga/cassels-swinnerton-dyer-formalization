import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import PfaffianDescent.CorayOriginalChartGenericLinearity
import AllCharacteristics.NormalizedChartGeneration

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal normalized homogeneous polynomial equals evaluation of its
SAME original through-point quotient section. -/
theorem cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n)
    (hClass : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1) :
    q.eval₂ (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j) =
      cubicThroughPointChartEvaluation p hp n y hpy j s := by
  let I := equationIdeal p hp
  have hGrade : (⟨Ideal.Quotient.mk I.toIdeal q,
      polynomial_class_mem_grading I q hq⟩ : grading I n) = s.1 := Subtype.ext hClass
  rw [eval₂_chartCoordinate_eq_fraction I j q hq]
  change gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n
    ⟨Ideal.Quotient.mk I.toIdeal q, polynomial_class_mem_grading I q hq⟩ =
      gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n s.1
  exact congrArg (gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n) hGrade

/-- A nonzero value of an ACTUAL through-P q0 forces one native evaluated
basis coordinate nonzero at the same auxiliary field point. No denominator
coordinate, basis extension or projective point is supplied. -/
theorem cubicThroughPointBasis_nonzero_polynomial_value_exists_nativeDenominator001
    {K L M : Type u} [Field K] [CommRing L] [Algebra K L] [Field M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q0 : MvPolynomial (Fin 4) K) (hq0 : q0.IsHomogeneous n)
    (hqP : q0.eval₂ (algebraMap K L) y = 0)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hqA : g (q0.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) ≠ 0) :
    ∃ a : Fin m, g (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0 := by
  classical
  let I := equationIdeal p hp
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let sGrade : grading I n :=
    ⟨Ideal.Quotient.mk I.toIdeal q0, polynomial_class_mem_grading I q0 hq0⟩
  have hMem : sGrade ∈ cubicThroughCoordinateSections p hp n y hpy :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy sGrade).mpr ⟨q0, hq0, hqP, rfl⟩
  let s : cubicThroughCoordinateSections p hp n y hpy := ⟨sGrade, hMem⟩
  have hNormalized := cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001
    p hp n y hpy j s q0 hq0 rfl
  by_contra h
  have hAll (a : Fin m) : g (e (b a)) = 0 := by
    by_contra ha
    exact h ⟨a, ha⟩
  have hSum : e s = ∑ i, chartBaseMap I j (b.repr s i) * e (b i) := by
    have hEval := congrArg e (b.sum_repr s)
    rw [map_sum] at hEval
    calc
      e s = ∑ i, e (b.repr s i • b i) := hEval.symm
      _ = ∑ i, chartBaseMap I j (b.repr s i) * e (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        exact gradedChartNative_smul_eq_baseMap_mul (grading I) (b.repr s i) (e (b i))
  apply hqA
  rw [hNormalized, hSum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, hAll, mul_zero]

end PfaffianDescent.Coray
