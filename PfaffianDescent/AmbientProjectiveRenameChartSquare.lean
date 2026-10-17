import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.GradedSurjection

/-! Exact ambient chart permutation for the original supplied coordinates.
The distinguished new chart is pulled back to its actual original chart;
the resulting morphism identity keeps the same coordinate algebra. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def ambientRenameGradedHom (pi : Equiv.Perm (Fin 4)) :
    homogeneousSubmodule (Fin 4) K →+*ᵍ homogeneousSubmodule (Fin 4) K where
  __ := (MvPolynomial.renameEquiv K pi).toRingHom
  map_mem hx := hx.rename_isHomogeneous

def ambientProjectiveRenameMap (pi : Equiv.Perm (Fin 4)) :
    Proj (homogeneousSubmodule (Fin 4) K) ⟶ Proj (homogeneousSubmodule (Fin 4) K) :=
  Proj.map (ambientRenameGradedHom pi)
    (gradedSurjective_irrelevant_le _ (MvPolynomial.renameEquiv K pi).surjective)

private theorem ambientRenameGradedHom_X (pi : Equiv.Perm (Fin 4)) (j : Fin 4) :
    ambientRenameGradedHom (K := K) pi (X j) = X (pi j) := rename_X pi j

def ambientRenameChartMap (pi : Equiv.Perm (Fin 4)) (j : Fin 4) :
    Away (homogeneousSubmodule (Fin 4) K) (X j) →+*
      Away (homogeneousSubmodule (Fin 4) K) (X (pi j)) :=
  AllCharacteristics.gradedAwayMapOfEq (ambientRenameGradedHom pi)
    (X j) (X (pi j)) (ambientRenameGradedHom_X pi j)

theorem ambientRenameChartMap_base (pi : Equiv.Perm (Fin 4)) (j : Fin 4) (c : K) :
    ambientRenameChartMap pi j
      (AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) K) (z := X j) c) =
      AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) K) (z := X (pi j)) c := by
  have hC : (C c : MvPolynomial (Fin 4) K) ∈
      homogeneousSubmodule (Fin 4) K (0 • 1) := by simpa using isHomogeneous_C c
  change AllCharacteristics.gradedAwayMapOfEq _ _ _ _
    (Away.mk _ (isHomogeneous_X K j) 0 (C c) hC) = _
  rw [AllCharacteristics.gradedAwayMapOfEq_mk _ _ _ _
    (isHomogeneous_X K j) (isHomogeneous_X K (pi j)) 0 (C c) hC]
  simp only [show ambientRenameGradedHom (K := K) pi (C c) = C c from rename_C pi c]
  rfl

theorem ambientRenameChartMap_coordinate
    (pi : Equiv.Perm (Fin 4)) (j r : Fin 4) :
    ambientRenameChartMap (K := K) pi j (ambientChartCoordinate (R := K) j r) =
      ambientChartCoordinate (R := K) (pi j) (pi r) := by
  unfold ambientRenameChartMap ambientChartCoordinate AllCharacteristics.GradedChart.normalized
  rw [AllCharacteristics.gradedAwayMapOfEq_mk _ _ _ _
    (isHomogeneous_X K j) (isHomogeneous_X K (pi j)) 1 (X r)
      (by simpa only [one_smul] using
        ((mem_homogeneousSubmodule 1 (X r : MvPolynomial (Fin 4) K)).mpr
          (isHomogeneous_X K r)))]
  simp only [ambientRenameGradedHom_X]

theorem ambientRenameChartMap_eval (pi : Equiv.Perm (Fin 4)) (j : Fin 4)
    (p : MvPolynomial (Fin 4) K) :
    ambientRenameChartMap pi j (ambientChartEvaluation j p) =
      ambientChartEvaluation (pi j) (rename pi p) := by
  have h : (ambientRenameChartMap (K := K) pi j).comp (ambientChartEvaluation (R := K) j) =
      (ambientChartEvaluation (R := K) (pi j)).comp (rename pi).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change ambientRenameChartMap pi j (ambientChartEvaluation j (C c)) =
        ambientChartEvaluation (pi j) (rename pi (C c))
      simp only [rename_C, ambientChartEvaluation, eval₂Hom_C]
      exact ambientRenameChartMap_base pi j c
    · intro r
      change ambientRenameChartMap pi j (ambientChartEvaluation j (X r)) =
        ambientChartEvaluation (pi j) (rename pi (X r))
      simp only [rename_X, ambientChartEvaluation, eval₂Hom_X']
      exact ambientRenameChartMap_coordinate pi j r
  exact DFunLike.congr_fun h p

/-- This derives the actual point permutation square from the same original
x, including the particular chart that contains the entire supplied scheme. -/
theorem ambientNormalizedCoordinateChartPoint_rename
    (x : Fin 4 → A) (pi : Equiv.Perm (Fin 4)) (j : Fin 4) (hx : x (pi j) = 1) :
    ambientNormalizedCoordinateChartPoint (F := K) x (pi j) hx ≫
      ambientProjectiveRenameMap (K := K) pi =
      ambientNormalizedCoordinateChartPoint (F := K) (fun r => x (pi r)) j hx := by
  have hmap : (ambientNormalizedCoordinateChartMap x (pi j) hx).comp
      (ambientRenameChartMap (K := K) pi j) =
      ambientNormalizedCoordinateChartMap (fun r => x (pi r)) j hx := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := K) j a
    change ambientNormalizedCoordinateChartMap x (pi j) hx
      (ambientRenameChartMap pi j (ambientChartEvaluation j p)) = _
    rw [ambientRenameChartMap_eval, ambientNormalizedCoordinateChartMap_eval]
    change aeval (R := K) x (rename pi p) =
      ambientNormalizedCoordinateChartMap (fun r => x (pi r)) j hx (ambientChartEvaluation j p)
    simpa only [ambientNormalizedCoordinateChartMap_eval, aeval_rename, Function.comp_def]
  unfold ambientNormalizedCoordinateChartPoint ambientProjectiveRenameMap
  rw [Category.assoc, AllCharacteristics.awayι_comp_map_of_eq
    (ambientRenameGradedHom pi)
    (gradedSurjective_irrelevant_le _ (MvPolynomial.renameEquiv K pi).surjective)
    (X j) (X (pi j)) (ambientRenameGradedHom_X pi j) (by decide : 0 < 1)
    (isHomogeneous_X K j) (isHomogeneous_X K (pi j)),
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom
      ((ambientNormalizedCoordinateChartMap x (pi j) hx).comp
        (ambientRenameChartMap (K := K) pi j))) ≫ _ = _
  rw [hmap]

/-- In the manuscript's actual chart normalization, pi 0=j comes from the
chosen original chart. No geometric permutation certificate is added. -/
theorem ambientNormalizedCoordinateChartPoint_rename_zero
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1)
    (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j) :
    ambientNormalizedCoordinateChartPoint (F := K) x j hx ≫
      ambientProjectiveRenameMap (K := K) pi =
      ambientNormalizedCoordinateChartPoint (F := K) (fun r => x (pi r)) 0
        (by rw [hpi]; exact hx) := by
  simpa only [hpi] using ambientNormalizedCoordinateChartPoint_rename x pi 0
    (by rw [hpi]; exact hx)

end PfaffianDescent
