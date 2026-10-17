import PfaffianDescent.ProjectivePositiveDifferencePairing
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-!
# Local invertibility of positive-result mixed projective-twist pairings

The pairings `O(5) ⊗ O(-4) → O(1)` and `O(5) ⊗ O(-3) → O(2)` are
isomorphisms on homogeneous polynomial quotients.  The latter is the middle
identification needed for the cubic hypersurface restriction sequence.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace ProjectiveNegativeTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- The equal-degree positive-result pairing is an isomorphism on every
homogeneous polynomial quotient. -/
theorem quotientPositiveNegativePositiveDifferencePairing_five_five_isIso
    (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativePositiveDifferencePairing (grading I) 5 5 (by omega)) := by
  let 𝓑 := grading I
  let h55 : 5 ≤ 5 := by omega
  let : IsIso (positiveZeroToZeroTwist 𝓑) :=
    (positiveZeroTwistIso 𝓑).isIso_hom
  let : IsIso (positiveNegativePairing 𝓑 5) :=
    quotientPositiveNegativePairing_isIso_all I 5
  have : IsIso (positiveNegativePositiveDifferencePairing 𝓑 5 5 h55 ≫
      positiveZeroToZeroTwist 𝓑) := by
    rw [positiveNegativePositiveDifferencePairing_five_five_factorization]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (positiveNegativePositiveDifferencePairing 𝓑 5 5 h55)
    (positiveZeroToZeroTwist 𝓑)

/-- On every coordinate chart, `O(5) ⊗ O(-4) → O(1)` is an isomorphism. -/
theorem quotientCoordinatePositiveNegativePositiveDifferencePairing_five_four_isIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativePositiveDifferencePairing (grading I) 5 4 (by omega))) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let h55 : 5 ≤ 5 := by omega
  let h54 : 4 ≤ 5 := by omega
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  let : IsIso (F.map (mulHomogeneous 𝓑 s 4)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s 4 hspan
  let : IsIso (F.map (positiveMulHomogeneous 𝓑 s 0)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s 0 hspan
  let : IsIso (positiveNegativePositiveDifferencePairing 𝓑 5 5 h55) :=
    quotientPositiveNegativePositiveDifferencePairing_five_five_isIso I
  let : IsIso (F.map (positiveNegativePositiveDifferencePairing 𝓑 5 5 h55)) := by
    infer_instance
  let : IsIso (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 4))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 4)
  have h := congrArg F.map
    (positiveNegativePositiveDifferencePairing_five_four_mul_naturality 𝓑 s)
  rw [F.map_comp, F.map_comp] at h
  have : IsIso (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 4)) ≫
      F.map (positiveNegativePositiveDifferencePairing 𝓑 5 4 h54)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 4)))
    (F.map (positiveNegativePositiveDifferencePairing 𝓑 5 4 h54))

/-- The `(5,4)` positive-result pairing is globally an isomorphism. -/
theorem quotientPositiveNegativePositiveDifferencePairing_five_four_isIso
    (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativePositiveDifferencePairing (grading I) 5 4 (by omega)) := by
  let h54 : 4 ≤ 5 := by omega
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let F : ∀ j : QuotientCoordinateIndex (σ := σ),
      (Proj (grading I)).Modules ⥤
        SheafOfModules ((Proj (grading I)).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  let : ∀ j, IsIso ((F j).map
      (positiveNegativePositiveDifferencePairing (grading I) 5 4 h54)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      let : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativePositiveDifferencePairing (grading I) 5 4 h54)) :=
        quotientCoordinatePositiveNegativePositiveDifferencePairing_five_four_isIso I j.down
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down)
        (positiveNegativePositiveDifferencePairing (grading I) 5 4 h54)
  exact hF.isIso (positiveNegativePositiveDifferencePairing (grading I) 5 4 h54)

/-- On every coordinate chart, `O(5) ⊗ O(-3) → O(2)` is an isomorphism. -/
theorem quotientCoordinatePositiveNegativePositiveDifferencePairing_five_three_isIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativePositiveDifferencePairing (grading I) 5 3 (by omega))) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let h54 : 4 ≤ 5 := by omega
  let h53 : 3 ≤ 5 := by omega
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  let : IsIso (F.map (mulHomogeneous 𝓑 s 3)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s 3 hspan
  let : IsIso (F.map (positiveMulHomogeneous 𝓑 s 1)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s 1 hspan
  let : IsIso (positiveNegativePositiveDifferencePairing 𝓑 5 4 h54) :=
    quotientPositiveNegativePositiveDifferencePairing_five_four_isIso I
  let : IsIso (F.map (positiveNegativePositiveDifferencePairing 𝓑 5 4 h54)) := by
    infer_instance
  let : IsIso (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 3))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 3)
  have h := congrArg F.map
    (positiveNegativePositiveDifferencePairing_five_three_mul_naturality 𝓑 s)
  rw [F.map_comp, F.map_comp] at h
  have : IsIso (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 3)) ≫
      F.map (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (F.map (schemeModuleTensorMap
      (𝟙 (positiveSheafOfModules 𝓑 5)) (mulHomogeneous 𝓑 s 3)))
    (F.map (positiveNegativePositiveDifferencePairing 𝓑 5 3 h53))

/-- The `(5,3)` positive-result pairing is globally an isomorphism. -/
theorem quotientPositiveNegativePositiveDifferencePairing_five_three_isIso
    (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativePositiveDifferencePairing (grading I) 5 3 (by omega)) := by
  let h53 : 3 ≤ 5 := by omega
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  let F : ∀ j : QuotientCoordinateIndex (σ := σ),
      (Proj (grading I)).Modules ⥤
        SheafOfModules ((Proj (grading I)).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj (grading I)).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U hU
  let : ∀ j, IsIso ((F j).map
      (positiveNegativePositiveDifferencePairing (grading I) 5 3 h53)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      let : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativePositiveDifferencePairing (grading I) 5 3 h53)) :=
        quotientCoordinatePositiveNegativePositiveDifferencePairing_five_three_isIso I j.down
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down)
        (positiveNegativePositiveDifferencePairing (grading I) 5 3 h53)
  exact hF.isIso (positiveNegativePositiveDifferencePairing (grading I) 5 3 h53)

/-- Tensoring the closed-immersion ideal sequence by the fifth positive
twist is short exact on every homogeneous polynomial quotient.  This is the
exactness input for the positively twisted cubic restriction sequence. -/
theorem quotientClosedImmersionIdealTwistSequence_five_shortExact
    (I : HomogeneousIdeal 𝒜) {Z : Scheme.{u}} (i : Z ⟶ Proj (grading I))
    [IsClosedImmersion i] :
    (closedImmersionIdealTwistSequence i
      (positiveSheafOfModules (grading I) 5)).ShortExact := by
  let U := quotientCoordinateOpenLifted I
  let hU : (Opens.grothendieckTopology (Proj (grading I))).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  apply closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    i U hU
  intro j
  dsimp [U, quotientCoordinateOpenLifted]
  exact overFunctorIsoUnit_of_restrictIsoUnit
    (quotientCoordinateOpen I j.down)
    (quotientCoordinatePositiveTwistUnitIso_all I j.down 5)

end ProjectiveNegativeTwist
end PfaffianDescent
