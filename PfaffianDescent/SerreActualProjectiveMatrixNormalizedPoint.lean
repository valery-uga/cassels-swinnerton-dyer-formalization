import PfaffianDescent.SerreActualProjectiveMatrixNormalizedChart

/-! The actual projective matrix morphism sends a normalized vector point
to the normalized point of its actual matrix-transformed vector. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem projectiveFrameCoordinateMap_normalized_point
    {K L : Type u} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) K) (hNM : N * M = 1) (x : Fin n → L)
    (z : CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (hz : z ∈ grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) 1)
    (hOneX : projectiveMatrixVectorEvaluation x (projectiveMatrixGradingMap M z) = 1) :
    let y := (M.map (algebraMap K L)).mulVec x
    let hOneY : projectiveMatrixVectorEvaluation y z = 1 :=
      (RingHom.congr_fun (projectiveMatrixVectorEvaluation_comp M x) z).symm.trans hOneX
    linearNormalizedPointAt
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) x
      (projectiveMatrixVectorEquations x) (projectiveMatrixGradingMap M z)
      ((projectiveMatrixGradingMap M).map_mem hz) hOneX ≫
        projectiveFrameCoordinateMap M N hNM =
      linearNormalizedPointAt
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) y
        (projectiveMatrixVectorEquations y) z hz hOneY := by
  dsimp only
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let F := projectiveMatrixGradingMap M
  let y := (M.map (algebraMap K L)).mulVec x
  let hOneY : projectiveMatrixVectorEvaluation y z = 1 :=
    (RingHom.congr_fun (projectiveMatrixVectorEvaluation_comp M x) z).symm.trans hOneX
  let bx := linearNormalizedPointChartMapAt I x (projectiveMatrixVectorEquations x)
    (F z) (F.map_mem hz) hOneX
  let by' := linearNormalizedPointChartMapAt I y (projectiveMatrixVectorEquations y)
    z hz hOneY
  have hspec : Spec.map (CommRingCat.ofHom bx) ≫
      Spec.map (CommRingCat.ofHom (Away.map F z)) =
      Spec.map (CommRingCat.ofHom by') := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    change CommRingCat.ofHom (bx.comp (Away.map F z)) = CommRingCat.ofHom by'
    exact congrArg CommRingCat.ofHom (projectiveMatrixNormalizedChartMap_comp M x z hz hOneX hOneY)
  change (Spec.map (CommRingCat.ofHom bx) ≫
    Proj.awayι (grading I) (F z) (F.map_mem hz) (by decide : 0 < 1)) ≫
      polynomialProjectiveMap I I (rectangularSubstitution M) bot_le
        (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
        (rectangularSubstitution_surjective M N hNM) =
    Spec.map (CommRingCat.ofHom by') ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have haway := awayι_polynomialProjectiveMap I I (rectangularSubstitution M)
    bot_le (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
    (rectangularSubstitution_surjective M N hNM) z hz (by decide : 0 < 1)
  calc
    _ = Spec.map (CommRingCat.ofHom bx) ≫
        (Proj.awayι (grading I) (F z) (F.map_mem hz) (by decide : 0 < 1) ≫
          polynomialProjectiveMap I I (rectangularSubstitution M) bot_le
            (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
            (rectangularSubstitution_surjective M N hNM)) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom bx) ≫
        (Spec.map (CommRingCat.ofHom (Away.map F z)) ≫
          Proj.awayι (grading I) z hz (by decide : 0 < 1)) :=
      congrArg (fun f => Spec.map (CommRingCat.ofHom bx) ≫ f) haway
    _ = (Spec.map (CommRingCat.ofHom bx) ≫
        Spec.map (CommRingCat.ofHom (Away.map F z))) ≫
          Proj.awayι (grading I) z hz (by decide : 0 < 1) := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1)) hspec

end PfaffianDescent
