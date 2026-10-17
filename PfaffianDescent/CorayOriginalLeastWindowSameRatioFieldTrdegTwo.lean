import PfaffianDescent.CorayOriginalLeastWindowNativeCurveBranchEndpoint
import PfaffianDescent.CorayAiOriginalRatioFieldImageDimensionOne
import PfaffianDescent.CorayOriginalCubicFunctionFieldTrdeg
import PfaffianDescent.CorayOriginalBasisRatioField
import Mathlib.SetTheory.Cardinal.Basic

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Cardinal bounds are kept as cardinals; no truncation to a natural
number or infinite-cardinal exclusion is assumed. -/
private theorem cardinal_eq_two_of_not_le_one_of_le_two001
    (c : Cardinal.{u}) (hNot : ¬ c ≤ 1) (hUpper : c ≤ 2) : c = 2 :=
  le_antisymm hUpper (Cardinal.two_le_iff_one_lt.mpr (lt_of_not_ge hNot))

/-- Failure of the honest curve bound for the SAME image forces degree>1
for the SAME existing ratio field. Its canonical inclusion into ORIGINAL F
and internally constructed F-degree2 give the exact upper bound2. -/
private theorem sameOriginalBasisRatioField_trdeg_two_of_image_not_curve001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m)
    (hNotCurve : ¬ ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
      Ring.DimensionLEOne
        ((cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a).presheaf.stalk z)) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    Algebra.trdeg K E = 2 := by
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  have hNotOne : ¬ Algebra.trdeg K E ≤ 1 := by
    intro hOne
    exact hNotCurve
      (cubicThroughPointOriginalBasisRatioField_trdeg_le_one_sameImage_stalk_dimensionLEOne001
        p hp hp0 n y hpy j b a hOne)
  have hUpper : Algebra.trdeg K E ≤ 2 :=
    (_root_.trdeg_le_of_injective E.val Subtype.val_injective).trans_eq
      (cubicOriginalFunctionField_trdeg_eq_two p hp j hp0)
  exact cardinal_eq_two_of_not_le_one_of_le_two001 (Algebra.trdeg K E) hNotOne hUpper

/-- Natural ORIGINAL least-point/no-section/window reduction now returns
4/n2,10/n3, or an internally constructed SAME original basis ratio field of
exact transcendence degree2. No E, degree, rank, image or map outcome premise.
This does not yet prove the remaining surface/tangent contradiction. -/
theorem coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_sameRatioField_trdeg_two001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    : let S := hypersurface p hp
    letI : IsIntegral S :=
      PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
    letI : Algebra K S.functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) ∨
      ∃ (j : Fin 4)
        (gP : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
        gP.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) ∧
        Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) j =
          S.fromSpecResidueField P.1 ∧
        ∃ (hpy : p.eval₂ (algebraMap K (S.residueField P.1))
            (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) = 0)
          (hChart : Nonempty (chartι (equationIdeal p hp) j).opensRange),
          letI := hChart
          ∃ (m : ℕ), 5 ≤ m ∧
            ∃ (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n
                (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy))
              (a : Fin m),
              let E := cubicThroughPointOriginalBasisRatioField p hp n
                (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b a
              Algebra.trdeg K E = 2 := by
  classical
  intro S
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  rcases coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_nativeImage_not_curve001
      p hp hp0 P hPointCoprime hleast hno n hLower hUpper with hFour | hTen | hImage
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  rcases hImage with ⟨j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a, hNotCurve⟩
  letI := hChart
  right
  right
  refine ⟨j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a, ?_⟩
  exact sameOriginalBasisRatioField_trdeg_two_of_image_not_curve001
    p hp hp0 n (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b a hNotCurve

end PfaffianDescent.Coray
