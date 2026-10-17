import PfaffianDescent.ProjectiveLinearCoordinateAmbientSquare
import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.AmbientNormalizedPointUnitChartComparison

/-! SOURCE ONLY, UNVERIFIED. The actual ambient GL map has the literal
matrix action on a vector normalized by its pulled-back target coordinate.
No projective-point comparison or ambient square is a hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The orientation is `.inv`: its polynomial map is substitution by M. -/
theorem actual_linear_frame_normalized_point_square
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (x : Fin 4 → A) (j : Fin 4)
    (hOne : (M.map (algebraMap K A)).mulVec x j = 1) :
    let ell := linearCoordinate M j
    let hell := linearCoordinate_homogeneous M j
    let hx : ell.eval₂ (algebraMap K A) x = 1 := by
      change aeval (R := K) x (linearCoordinate M j) = 1
      rw [linearCoordinate_aeval, hOne]
    let he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K A) x = 0 := fun p hp => by
        have hp0 : p = 0 := Ideal.mem_bot.mp hp
        simp [hp0]
    (linearNormalizedPoint ⊥ x ell hell hx he ≫ quotientProjMap ⊥) ≫
        (linearCoordinateChangeAmbientIso M hM).inv =
      ambientNormalizedCoordinateChartPoint (F := K)
        ((M.map (algebraMap K A)).mulVec x) j hOne := by
  dsimp only
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let ell := linearCoordinate M j
  have hell : ell.IsHomogeneous 1 := linearCoordinate_homogeneous M j
  have hx : ell.eval₂ (algebraMap K A) x = 1 := by
    change aeval (R := K) x (linearCoordinate M j) = 1
    rw [linearCoordinate_aeval, hOne]
  have he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    have hp0 : p = 0 := Ideal.mem_bot.mp hp
    simp [hp0]
  let F := linearCoordinateChangeAmbientGradedHom M
  have hF : Function.Surjective F := (linearSubstitutionEquiv M hM).surjective
  let G := (quotientGradedRingHom I).comp F
  have hG : Function.Surjective G := (quotientGradedRingHom_surjective I).comp hF
  let hg := gradedSurjective_irrelevant_le G hG
  let z := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  have hGz : G (X j) = z := by
    change Ideal.Quotient.mk I.toIdeal (linearSubstitution M (X j)) = _
    rw [linearSubstitution_X]
  let phi := AllCharacteristics.gradedAwayMapOfEq G (X j) z hGz
  let e := Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K A) x) he
  have hez : e z = 1 := hx
  let psi := linearNormalizedPointChartMap I x ell hx he
  have hPhiCoordinate (r : Fin 4) :
      psi (phi (ambientChartCoordinate (R := K) j r)) =
        (M.map (algebraMap K A)).mulVec x r := by
    dsimp only [phi]
    unfold ambientChartCoordinate AllCharacteristics.GradedChart.normalized
    rw [AllCharacteristics.gradedAwayMapOfEq_mk G (X j) z hGz
      (isHomogeneous_X K j) hz 1 (X r)
      (by simpa only [one_smul] using
        ((mem_homogeneousSubmodule 1 (X r : MvPolynomial (Fin 4) K)).mpr
          (isHomogeneous_X K r)))]
    change AllCharacteristics.GradedChart.liftCoordinateOne (grading I) z e hez
      (Away.mk (grading I) hz 1 (G (X r)) _) = _
    rw [AllCharacteristics.GradedChart.liftCoordinateOne_mk]
    change aeval (R := K) x (linearSubstitution M (X r)) = _
    rw [linearSubstitution_X, linearCoordinate_aeval]
  have hPhiBase (c : K) :
      psi (phi (AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) K) (z := X j) c)) = algebraMap K A c := by
    have hC : (C c : MvPolynomial (Fin 4) K) ∈
        homogeneousSubmodule (Fin 4) K (0 • 1) := by simpa using isHomogeneous_C c
    change psi (AllCharacteristics.gradedAwayMapOfEq G (X j) z hGz
      (Away.mk _ (isHomogeneous_X K j) 0 (C c) hC)) = _
    rw [AllCharacteristics.gradedAwayMapOfEq_mk G (X j) z hGz
      (isHomogeneous_X K j) hz 0 (C c) hC]
    change AllCharacteristics.GradedChart.liftCoordinateOne (grading I) z e hez
      (Away.mk (grading I) hz 0 (G (C c)) _) = _
    rw [AllCharacteristics.GradedChart.liftCoordinateOne_mk]
    change aeval (R := K) x (linearSubstitution M (C c)) = _
    simp
  have hMap : psi.comp phi = ambientNormalizedCoordinateChartMap
      ((M.map (algebraMap K A)).mulVec x) j hOne := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := K) j a
    change psi (phi (ambientChartEvaluation j p)) = _
    rw [ambientNormalizedCoordinateChartMap_eval]
    have heval : (psi.comp phi).comp (ambientChartEvaluation (R := K) j) =
        eval₂Hom (algebraMap K A) ((M.map (algebraMap K A)).mulVec x) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simpa only [RingHom.comp_apply, ambientChartEvaluation, eval₂Hom_C]
          using hPhiBase c
      · intro r
        simpa only [RingHom.comp_apply, ambientChartEvaluation, eval₂Hom_X']
          using hPhiCoordinate r
    exact DFunLike.congr_fun heval p
  have hChart : linearNormalizedPoint I x ell hell hx he ≫ Proj.map G hg =
      ambientNormalizedCoordinateChartPoint
        ((M.map (algebraMap K A)).mulVec x) j hOne := by
    unfold linearNormalizedPoint ambientNormalizedCoordinateChartPoint
    dsimp only
    rw [Category.assoc, AllCharacteristics.awayι_comp_map_of_eq G hg (X j) z hGz
      (by decide : 0 < 1) (isHomogeneous_X K j) hz,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (psi.comp phi)) ≫ _ = _
    rw [hMap]
  change (linearNormalizedPoint I x ell hell hx he ≫ quotientProjMap I) ≫
    Proj.map F (gradedSurjective_irrelevant_le F hF) = _
  unfold quotientProjMap
  rw [Category.assoc, ← Proj.map_comp F (quotientGradedRingHom I)
    (gradedSurjective_irrelevant_le F hF) (irrelevant_le_map_quotientGradedRingHom I)]
  exact hChart

end PfaffianDescent
