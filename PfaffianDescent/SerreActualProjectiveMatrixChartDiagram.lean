import PfaffianDescent.SerreActualGradedChartLift
import PfaffianDescent.SerreActualGradedOverlapChartMap
import PfaffianDescent.SerreActualProjectiveMatrixOverlapRestriction
import PfaffianDescent.SchemeAffineFunctions

/-! A commuting actual projective matrix diagram gives the normalized
coefficient comparison on the whole source scheme. Its normalization ratio
is an actual invertible regular function, derived from the chart maps. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveMatrixChartDiagram_regular_coordinates
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hF : HomogeneousIdeal.irrelevant
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≤
      (HomogeneousIdeal.irrelevant
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))).map
          (projectiveMatrixGradingMap M))
    (f z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hf : f ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    {T : Scheme.{u}}
    (a : T ⟶ Spec (.of (Away
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) f)))
    (b : T ⟶ Spec (.of (Away
      (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) z)))
    (h : (a ≫ Proj.awayι
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) f hf
        (by decide : 0 < 1)) ≫ Proj.map (projectiveMatrixGradingMap M) hF =
      b ≫ Proj.awayι
        (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) z hz
        (by decide : 0 < 1)) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
    let β := (affineFunctionHom a).comp
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := f))
    ∃ u : Γ(T, ⊤), IsUnit u ∧ ∀ i,
      affineFunctionHom b (linearChartCoordinate I z hz i) =
        u * ((M.map β).mulVec
          (fun j => affineFunctionHom a (linearChartCoordinate I f hf j))) i := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  let g := F z
  have hg : g ∈ grading I 1 := F.map_mem hz
  let k := a ≫ Proj.awayι (grading I) f hf (by decide : 0 < 1)
  let pre := serreActualGradedChartLift (grading I) (grading I) F hF z hz k b h
  have hp : pre ≫ Proj.awayι (grading I) g hg (by decide : 0 < 1) = k :=
    serreActualGradedChartLift_toProj (grading I) (grading I) F hF z hz k b h
  let o := serreActualGradedOverlapChartMap (grading I) f g hf hg a pre hp.symm
  let φ := affineFunctionHom o
  let φold : Away (grading I) f →+* Away (grading I) (f * g) :=
    awayMap (grading I) hg rfl
  let φnew : Away (grading I) g →+* Away (grading I) (f * g) :=
    awayMap (grading I) hf (mul_comm f g)
  let βf := AllCharacteristics.GradedChart.baseMap (grading I) (z := f)
  let βfg := AllCharacteristics.GradedChart.baseMap (grading I) (z := f * g)
  let u := AllCharacteristics.GradedChart.overlapCoordinateUnit (grading I) hf hg
  have hlmap : o ≫ Spec.map (CommRingCat.ofHom φold) = a :=
    serreActualGradedOverlapChartMap_left (grading I) f g hf hg a pre hp.symm
  have hrmap : (o ≫ Spec.map (CommRingCat.ofHom φnew)) ≫
      Spec.map (CommRingCat.ofHom (Away.map F z)) = b := by
    calc
      _ = pre ≫ Spec.map (CommRingCat.ofHom (Away.map F z)) :=
        congrArg (fun m => m ≫ Spec.map (CommRingCat.ofHom (Away.map F z)))
          (serreActualGradedOverlapChartMap_right (grading I) f g hf hg a pre hp.symm)
      _ = b := serreActualGradedChartLift_toChart
        (grading I) (grading I) F hF z hz k b h
  have hl : φ.comp φold = affineFunctionHom a := by
    have hs := congrArg affineFunctionHom hlmap
    rw [affineFunctionHom_comp_Spec] at hs
    exact hs
  have hr : (φ.comp φnew).comp (Away.map F z) = affineFunctionHom b := by
    have hs := congrArg affineFunctionHom hrmap
    rw [affineFunctionHom_comp_Spec, affineFunctionHom_comp_Spec] at hs
    exact hs
  have hbase : βfg = φold.comp βf := by
    apply RingHom.ext
    intro r
    exact (AllCharacteristics.GradedChart.awayMap_baseMap (grading I) hg rfl r).symm
  have hβ : φ.comp βfg = (affineFunctionHom a).comp βf := by
    rw [hbase, ← RingHom.comp_assoc, hl]
  refine ⟨φ (u : Away (grading I) (f * g)), u.isUnit.map φ, ?_⟩
  intro i
  calc
    affineFunctionHom b (linearChartCoordinate I z hz i) =
        φ (φnew ((Away.map F z) (linearChartCoordinate I z hz i))) :=
      (RingHom.congr_fun hr (linearChartCoordinate I z hz i)).symm
    _ = φ (u : Away (grading I) (f * g)) *
        ((M.map (φ.comp βfg)).mulVec
          (fun j => φ (φold (linearChartCoordinate I f hf j)))) i :=
      projectiveMatrixOverlap_restricted_normalized_coordinates M f z hf hz φ i
    _ = _ := by
      rw [hβ]
      have hv : (fun j => φ (φold (linearChartCoordinate I f hf j))) =
          (fun j => affineFunctionHom a (linearChartCoordinate I f hf j)) :=
        funext (fun j => RingHom.congr_fun hl (linearChartCoordinate I f hf j))
      rw [hv]

end PfaffianDescent
