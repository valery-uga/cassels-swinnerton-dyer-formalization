import PfaffianDescent.CorayGradedCoordinateMultiplication
import PfaffianDescent.CorayOriginalChartGenericEvaluation

/-! Source only, unverified. A genuine lower-degree through-P section
gives actual SAME-degree coordinate multiples whose generic ratios recover
the original ambient chart coordinates. This is only a branch prerequisite;
it does not assert that the Coray minimal-degree branch has such a section. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]

/-- Multiply a through-P quotient section by an actual quotient-grade
section. Membership is proved by the original coordinate algebra map. -/
def cubicThroughPointSectionProduct
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a b : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (s : cubicThroughCoordinateSections p hp a y hpy)
    (t : grading (equationIdeal p hp) b) :
    cubicThroughCoordinateSections p hp (a + b) y hpy :=
  ⟨gradeSectionProduct (grading (equationIdeal p hp)) s.1 t, by
    change cubicCoordinateAlgebraEvaluation p hp y hpy (s.1.1 * t.1) = 0
    rw [map_mul, show cubicCoordinateAlgebraEvaluation p hp y hpy s.1.1 = 0 from s.2,
      zero_mul]⟩

theorem cubicThroughPointChartEvaluation_sectionProduct
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a b : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp a y hpy)
    (t : grading (equationIdeal p hp) b) :
    cubicThroughPointChartEvaluation p hp (a + b) y hpy j
        (cubicThroughPointSectionProduct p hp a b y hpy s t) =
      cubicThroughPointChartEvaluation p hp a y hpy j s *
        gradedChartSectionEvaluation (grading (equationIdeal p hp))
          (coordinate_mem (equationIdeal p hp) j) b t := by
  change gradedChartSectionEvaluation (grading (equationIdeal p hp))
      (coordinate_mem (equationIdeal p hp) j) (a + b)
      (gradeSectionProduct (grading (equationIdeal p hp)) s.1 t) = _
  exact gradedChartSectionEvaluation_product (grading (equationIdeal p hp))
    (coordinate_mem (equationIdeal p hp) j) s.1 t

/-- Actual coordinate multiplication retains the original point kernel. -/
def cubicThroughPointCoordinateMultiple
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (s : cubicThroughCoordinateSections p hp a y hpy) (i : Fin 4) :
    cubicThroughCoordinateSections p hp (a + 1) y hpy :=
  cubicThroughPointSectionProduct p hp a 1 y hpy s
    ⟨coordinate (equationIdeal p hp) i, coordinate_mem (equationIdeal p hp) i⟩

theorem cubicThroughPointChartEvaluation_coordinateMultiple
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp a y hpy) (i : Fin 4) :
    cubicThroughPointChartEvaluation p hp (a + 1) y hpy j
        (cubicThroughPointCoordinateMultiple p hp a y hpy s i) =
      cubicThroughPointChartEvaluation p hp a y hpy j s *
        chartCoordinate (equationIdeal p hp) j i := by
  unfold cubicThroughPointCoordinateMultiple
  rw [cubicThroughPointChartEvaluation_sectionProduct]
  rfl

/-- Padding by the SAME chart coordinate permits every larger degree. -/
def cubicThroughPointCoordinatePadding
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a k : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp a y hpy) :
    cubicThroughCoordinateSections p hp (a + k) y hpy :=
  cubicThroughPointSectionProduct p hp a k y hpy s
    (gradeChartCoordinatePower (grading (equationIdeal p hp))
      (coordinate_mem (equationIdeal p hp) j) k)

theorem cubicThroughPointChartEvaluation_coordinatePadding
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (a k : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp a y hpy) :
    cubicThroughPointChartEvaluation p hp (a + k) y hpy j
        (cubicThroughPointCoordinatePadding p hp a k y hpy j s) =
      cubicThroughPointChartEvaluation p hp a y hpy j s := by
  unfold cubicThroughPointCoordinatePadding
  rw [cubicThroughPointChartEvaluation_sectionProduct,
    gradedChartSectionEvaluation_coordinatePower, mul_one]

end

section
variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
  [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
variable (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
  (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]

include hp0 in
/-- The ratio of actual degree-(a+k+1) through-P coordinate multiples
recovers every original ambient coordinate. Nonzero denominator is proved
from actual prime-cone and generic-germ injectivity, not supplied. -/
theorem cubicThroughPointGeneric_coordinateMultiples_recover
    (a k : ℕ) (s : cubicThroughCoordinateSections p hp a y hpy) (hs : s ≠ 0) :
    let t : Fin 4 → cubicThroughCoordinateSections p hp (a + k + 1) y hpy :=
      fun i => cubicThroughPointCoordinateMultiple p hp (a + k) y hpy
        (cubicThroughPointCoordinatePadding p hp a k y hpy j s) i
    cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t j) ≠ 0 ∧
      ∀ i : Fin 4,
        cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t i) /
          cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t j) =
        @affineChartGenericEvaluation
          (ChartRing (equationIdeal p hp) j)
          (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
          (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
          (chartι (equationIdeal p hp) j)
          (isOpenImmersion_chartι (equationIdeal p hp) j)
          (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
          (chartCoordinate (equationIdeal p hp) j i) := by
  let g := @affineChartGenericEvaluation
    (ChartRing (equationIdeal p hp) j)
    (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι (equationIdeal p hp) j)
    (isOpenImmersion_chartι (equationIdeal p hp) j)
    (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  let t : Fin 4 → cubicThroughCoordinateSections p hp (a + k + 1) y hpy :=
    fun i => cubicThroughPointCoordinateMultiple p hp (a + k) y hpy
      (cubicThroughPointCoordinatePadding p hp a k y hpy j s) i
  have hvalue (i : Fin 4) :
      cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t i) =
        g (cubicThroughPointChartEvaluation p hp a y hpy j s) *
          g (chartCoordinate (equationIdeal p hp) j i) := by
    change g (cubicThroughPointChartEvaluation p hp (a + k + 1) y hpy j (t i)) = _
    dsimp only [t]
    rw [cubicThroughPointChartEvaluation_coordinateMultiple,
      cubicThroughPointChartEvaluation_coordinatePadding, map_mul]
  have hbase : g (cubicThroughPointChartEvaluation p hp a y hpy j s) ≠ 0 := by
    intro hzero
    have hc : cubicThroughPointChartEvaluation p hp a y hpy j s = 0 :=
      (@affineChartGenericEvaluation_injective
        (ChartRing (equationIdeal p hp) j)
        (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
        (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
        (chartι (equationIdeal p hp) j)
        (isOpenImmersion_chartι (equationIdeal p hp) j)
        (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange))
        (hzero.trans (map_zero g).symm)
    apply hs
    exact cubicThroughPointChartEvaluation_injective p hp hp0 a y hpy j
      (hc.trans (map_zero (cubicThroughPointChartEvaluation p hp a y hpy j)).symm)
  have hj : cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t j) =
      g (cubicThroughPointChartEvaluation p hp a y hpy j s) := by
    rw [hvalue, chartCoordinate_self, map_one, mul_one]
  constructor
  · exact hj.symm ▸ hbase
  · intro i
    rw [hvalue, hj]
    exact mul_div_cancel_left₀ _ hbase

include hp0 in
/-- A genuine ground polynomial produces the above actual sections. The
natural lower-degree premise is explicit; no existence of it is claimed. -/
theorem cubicThroughPoint_lowerDegreePolynomial_exists_coordinateRecovery
    (a k : ℕ) (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous a)
    (hy : q.eval₂ (algebraMap K L) y = 0)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    ∃ t : Fin 4 → cubicThroughCoordinateSections p hp (a + k + 1) y hpy,
      cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t j) ≠ 0 ∧
        ∀ i : Fin 4,
          cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t i) /
            cubicThroughPointGenericEvaluation p hp (a + k + 1) y hpy j (t j) =
          @affineChartGenericEvaluation
            (ChartRing (equationIdeal p hp) j)
            (inferInstance : CommRing (ChartRing (equationIdeal p hp) j))
            (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
            (chartι (equationIdeal p hp) j)
            (isOpenImmersion_chartι (equationIdeal p hp) j)
            (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
            (chartCoordinate (equationIdeal p hp) j i) := by
  let sq : grading (equationIdeal p hp) a :=
    ⟨Ideal.Quotient.mk (equationIdeal p hp).toIdeal q, ⟨q, hq, rfl⟩⟩
  have hs : sq ∈ cubicThroughCoordinateSections p hp a y hpy :=
    (cubicThroughCoordinateSections_mem_iff p hp a y hpy sq).mpr ⟨q, hq, hy, rfl⟩
  let s : cubicThroughCoordinateSections p hp a y hpy := ⟨sq, hs⟩
  have hs0 : s ≠ 0 := by
    intro hzero
    have hv : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = 0 :=
      congrArg (fun z : cubicThroughCoordinateSections p hp a y hpy => z.1.1) hzero
    apply hnot
    exact Ideal.Quotient.eq_zero_iff_mem.mp hv
  exact ⟨_, cubicThroughPointGeneric_coordinateMultiples_recover
    p hp hp0 y hpy j a k s hs0⟩

end
end PfaffianDescent.Coray
end
