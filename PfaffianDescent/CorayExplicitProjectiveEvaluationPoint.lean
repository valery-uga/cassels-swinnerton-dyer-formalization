import AllCharacteristics.ProjectiveSpaceChartEvaluation

/-! Source-only / unverified. An actual coordinate vector with a specified
nonzero entry defines a projective point through the actual chart ring.
The normalized coordinate formula is exported, so the vector is not lost
inside an existence-only proposition. No algebra action is chosen. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K F : Type u} [CommRing K] [Field F] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual supplied vector, normalized by its specified chart entry. -/
def projectiveEvaluationRatios (x : σ → F) (j : σ) : σ → F :=
  fun i => x i / x j

theorem projectiveEvaluationRatios_self (x : σ → F) (j : σ) (hj : x j ≠ 0) :
    projectiveEvaluationRatios x j j = 1 := div_self hj

/-- Actual chart evaluation; it is defined from the supplied coordinates,
not by choosing a witness of a proposition that forgets those coordinates. -/
def projectiveEvaluationChartMap (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0) :
    ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j →+* F :=
  projectiveChartMap f (projectiveEvaluationRatios x j) j
    (projectiveEvaluationRatios_self x j hj)

theorem projectiveEvaluationChartMap_base (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0) :
    (projectiveEvaluationChartMap f x j hj).comp
      (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j) = f := by
  ext c
  exact projectiveChartMap_baseMap f (projectiveEvaluationRatios x j) j
    (projectiveEvaluationRatios_self x j hj) c

/-- The exact normalized coordinate law retains BOTH numerator and
denominator from the actual vector. -/
theorem projectiveEvaluationChartMap_coordinate (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0) (i : σ) :
    projectiveEvaluationChartMap f x j hj
      (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j i) =
        x i / x j :=
  projectiveChartMap_coordinate f (projectiveEvaluationRatios x j) j
    (projectiveEvaluationRatios_self x j hj) i

/-- The point is the Spec map of the ACTUAL normalized chart evaluation
followed by the ACTUAL chart open immersion. -/
def projectiveEvaluationPoint (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0) :
    Spec (.of F) ⟶ scheme
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) :=
  Spec.map (CommRingCat.ofHom (projectiveEvaluationChartMap f x j hj)) ≫
    chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j

theorem projectiveEvaluationPoint_toBase (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0) :
    projectiveEvaluationPoint f x j hj ≫
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) =
        Spec.map (CommRingCat.ofHom f) := by
  change (Spec.map (CommRingCat.ofHom (projectiveEvaluationChartMap f x j hj)) ≫
    chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j) ≫ _ = _
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((projectiveEvaluationChartMap f x j hj).comp
    (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j))) = _
  rw [projectiveEvaluationChartMap_base]

/-- Every chart-ring presentation of this SAME projective point is the
actual evaluated chart map. Thus the coordinate law applies to arbitrary
presentations of the point as well, not merely to its stored constructor. -/
theorem projectiveEvaluationPoint_chart_hom_eq (f : K →+* F) (x : σ → F)
    (j : σ) (hj : x j ≠ 0)
    (g : ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j →+* F)
    (hg : Spec.map (CommRingCat.ofHom g) ≫
      chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j =
        projectiveEvaluationPoint f x j hj) :
    g = projectiveEvaluationChartMap f x j hj :=
  chart_hom_eq_of_projective_eq
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) g
    (projectiveEvaluationChartMap f x j hj) hg

end PfaffianDescent.Coray
end
