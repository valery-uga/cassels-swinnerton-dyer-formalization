import PfaffianDescent.ProjectiveMixedTwistPairing
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal

/-!
# Local invertibility of the mixed projective-twist pairing

The degree `(2,3)` mixed pairing needed for the cubic surface restriction
sequence is an isomorphism on every standard affine chart.
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

/-- On every coordinate chart of a homogeneous polynomial quotient, the
mixed pairing `O(2) ⊗ O(-3) → O(-1)` is an isomorphism. -/
theorem quotientCoordinatePositiveNegativeDifferencePairing_two_three_isIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativeDifferencePairing (grading I) 2 3 h23)) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let h23 : 2 ≤ 3 := by omega
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  let : IsIso (F.map (positiveMulHomogeneous 𝓑 s 2)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s 2 hspan
  let : IsIso (F.map (mulHomogeneous 𝓑 s 0)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s 0 hspan
  let : IsIso (F.map (positiveNegativePairing 𝓑 3)) := by
    exact quotientCoordinatePositiveNegativePairing_isIso_all I j 3
  let : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous 𝓑 s 2) (𝟙 (sheafOfModules 𝓑 3)))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous 𝓑 s 2) (𝟙 (sheafOfModules 𝓑 3))
  have h := congrArg F.map
    (positiveNegativeDifferencePairing_two_three_mul_naturality 𝓑 s)
  rw [F.map_comp, F.map_comp] at h
  have : IsIso (F.map (positiveNegativeDifferencePairing 𝓑 2 3 h23) ≫
      F.map (mulHomogeneous 𝓑 s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (g := F.map (positiveNegativeDifferencePairing 𝓑 2 3 h23))
    (f := F.map (mulHomogeneous 𝓑 s 0))

/-- The mixed degree `(2,3)` pairing is globally an isomorphism on every
homogeneous polynomial quotient. -/
theorem quotientPositiveNegativeDifferencePairing_two_three_isIso
    (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativeDifferencePairing (grading I) 2 3 (by omega)) := by
  let h23 : 2 ≤ 3 := by omega
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
      (positiveNegativeDifferencePairing (grading I) 2 3 h23)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      let : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativeDifferencePairing (grading I) 2 3 h23)) :=
        quotientCoordinatePositiveNegativeDifferencePairing_two_three_isIso I j.down
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down)
        (positiveNegativeDifferencePairing (grading I) 2 3 h23)
  exact hF.isIso (positiveNegativeDifferencePairing (grading I) 2 3 h23)

/-- On every coordinate chart, the mixed pairing
`O(5) ⊗ O(-6) → O(-1)` is an isomorphism. -/
theorem quotientCoordinatePositiveNegativeDifferencePairing_five_six_isIso
    (I : HomogeneousIdeal 𝒜) (j : σ) :
    IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen I j).ι).map
      (positiveNegativeDifferencePairing (grading I) 5 6 (by omega))) := by
  let 𝓑 := grading I
  let U := quotientCoordinateOpen I j
  let F := Scheme.Modules.restrictFunctor U.ι
  let h56 : 5 ≤ 6 := by omega
  let s : 𝓑 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let hspan : (HomogeneousIdeal.irrelevant 𝓑).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝓑 1 => (f : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne 𝒜 𝓑
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  let : IsIso (F.map (positiveMulHomogeneous 𝓑 s 5)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝓑 s 5 hspan
  let : IsIso (F.map (mulHomogeneous 𝓑 s 0)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen 𝓑 s 0 hspan
  let : IsIso (F.map (positiveNegativePairing 𝓑 6)) := by
    exact quotientCoordinatePositiveNegativePairing_isIso_all I j 6
  let : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous 𝓑 s 5) (𝟙 (sheafOfModules 𝓑 6)))) := by
    exact restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous 𝓑 s 5) (𝟙 (sheafOfModules 𝓑 6))
  have h := congrArg F.map
    (positiveNegativeDifferencePairing_five_six_mul_naturality 𝓑 s)
  rw [F.map_comp, F.map_comp] at h
  have : IsIso (F.map (positiveNegativeDifferencePairing 𝓑 5 6 h56) ≫
      F.map (mulHomogeneous 𝓑 s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (g := F.map (positiveNegativeDifferencePairing 𝓑 5 6 h56))
    (f := F.map (mulHomogeneous 𝓑 s 0))

/-- The mixed degree `(5,6)` pairing is globally an isomorphism on every
homogeneous polynomial quotient. -/
theorem quotientPositiveNegativeDifferencePairing_five_six_isIso
    (I : HomogeneousIdeal 𝒜) :
    IsIso (positiveNegativeDifferencePairing (grading I) 5 6 (by omega)) := by
  let h56 : 5 ≤ 6 := by omega
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
      (positiveNegativeDifferencePairing (grading I) 5 6 h56)) :=
    fun j => by
      dsimp [F, U, quotientCoordinateOpenLifted]
      let : IsIso ((Scheme.Modules.restrictFunctor
          (quotientCoordinateOpen I j.down).ι).map
          (positiveNegativeDifferencePairing (grading I) 5 6 h56)) :=
        quotientCoordinatePositiveNegativeDifferencePairing_five_six_isIso I j.down
      exact overFunctorMap_isIso_of_restrictMap_isIso
        (quotientCoordinateOpen I j.down)
        (positiveNegativeDifferencePairing (grading I) 5 6 h56)
  exact hF.isIso (positiveNegativeDifferencePairing (grading I) 5 6 h56)

end ProjectiveNegativeTwist
end PfaffianDescent
