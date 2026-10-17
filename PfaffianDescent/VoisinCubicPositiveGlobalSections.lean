import PfaffianDescent.P3PositiveTwistGlobalSections
import PfaffianDescent.VoisinHypersurfaceCrossingTwist
import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.ProjectiveFiniteOfHilbertBound

/-!
# Global sections of the positive two-twist on a cubic surface

This file combines ambient positive-twist generation with the cubic
restriction sequence.  It proves that every intrinsic section of `O(2)` on a
smooth cubic surface is represented by a degree-two element of its homogeneous
coordinate ring.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

lemma localRingHom_mk_one
    {R P : Type*} [CommRing R] [CommRing P]
    (I : Ideal R) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : R →+* P) (hIJ : I = Ideal.comap f J) (x : R) :
    Localization.localRingHom I J f hIJ
        (Localization.mk x ⟨1, Submonoid.one_mem _⟩) =
      Localization.mk (f x) ⟨1, Submonoid.one_mem _⟩ := by
  rw [Localization.localRingHom_mk]
  congr 1
  simp

/-- Restricting an ambient homogeneous section to a cubic hypersurface gives
the homogeneous section defined by its quotient-coordinate-ring class. -/
theorem cubicCrossingTwistRestrictionSections_positiveGlobalSection
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : PS 2) :
    cubicCrossingTwistRestrictionSections K p hp
        (positiveGlobalSectionOfHomogeneous PS 2 q) =
      positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2
        ⟨(quotientGradedRingHom (equationIdeal p hp)) q,
          (quotientGradedRingHom (equationIdeal p hp)).map_mem q.property⟩ := by
  apply PresheafOfModules.sections_ext
  intro U
  apply Subtype.ext
  funext y
  change Localization.localRingHom _ _
      (quotientGradedRingHom (equationIdeal p hp)).toRingHom rfl
      (Localization.mk (q : MvPolynomial (Fin 4) K)
        ⟨1, Submonoid.one_mem _⟩) =
    Localization.mk
      ((quotientGradedRingHom (equationIdeal p hp))
        (q : MvPolynomial (Fin 4) K))
      ⟨1, Submonoid.one_mem _⟩
  exact localRingHom_mk_one _ _
    (quotientGradedRingHom (equationIdeal p hp)).toRingHom rfl
    (q : MvPolynomial (Fin 4) K)

/-- Degree-two homogeneous elements generate every global `O(2)` section on
a smooth cubic surface. -/
theorem cubic_positiveGlobalSectionOfHomogeneous_surjective_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules] :
    Function.Surjective
      (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2) := by
  intro t
  obtain ⟨s, hs⟩ :=
    cubicCrossingTwistRestrictionSections_surjective_of_smooth K p hp hp0 t
  obtain ⟨q, hq⟩ := p3_positiveGlobalSectionOfHomogeneous_surjective K 2 (by decide) s
  let qbar : grading (equationIdeal p hp) 2 :=
    ⟨(quotientGradedRingHom (equationIdeal p hp)) q,
      (quotientGradedRingHom (equationIdeal p hp)).map_mem q.property⟩
  refine ⟨qbar, ?_⟩
  calc
    positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 2 qbar =
        cubicCrossingTwistRestrictionSections K p hp
          (positiveGlobalSectionOfHomogeneous PS 2 q) :=
      (cubicCrossingTwistRestrictionSections_positiveGlobalSection K p hp q).symm
    _ = cubicCrossingTwistRestrictionSections K p hp s :=
      congrArg (cubicCrossingTwistRestrictionSections K p hp) hq
    _ = t := hs

/-- The finite-subsheme nonvanishing criterion on a smooth cubic surface,
with the global-generation premise discharged. -/
theorem cubic_finiteProjectiveClosedSubschemePositiveTwo_not_cohomology_one_subsingleton
    [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (scheme (equationIdeal p hp)).Modules]
    (hnot : ¬ Function.Surjective
      (finiteProjectiveClosedSubschemePositiveTwoRestriction
        (equationIdeal p hp) i)) :
    ¬ Subsingleton (schemeModuleCohomology (scheme (equationIdeal p hp))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 2)) 1) := by
  exact finiteProjectiveClosedSubschemePositiveTwo_not_cohomology_one_subsingleton
    (equationIdeal p hp) i
    (cubic_positiveGlobalSectionOfHomogeneous_surjective_of_smooth K p hp hp0)
    hnot

theorem cubic_length_eleven_positiveTwoRestriction_not_surjective
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    (hlen : AllCharacteristics.finiteSchemeRank
      (i ≫ toBase (equationIdeal p hp)) = 11) :
    ¬ Function.Surjective
      (finiteProjectiveClosedSubschemePositiveTwoRestriction
        (equationIdeal p hp) i) := by
  letI := finiteSchemeCoefficientAlgebra
    (i ≫ toBase (equationIdeal p hp))
  haveI : Module.Finite K Γ(Z, ⊤) :=
    finiteSchemeCoefficient_finite (i ≫ toBase (equationIdeal p hp))
  letI : Module.Finite K (grading (equationIdeal p hp) 2) :=
    polynomialQuotientGrade_finite (equationIdeal p hp) 2
  let f := finiteProjectiveClosedSubschemePositiveTwoRestrictionLinearMap (equationIdeal p hp) i
  intro hsurj
  have hf : Function.Surjective f := hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective hf
  rw [finiteSchemeCoefficient_finrank (i ≫ toBase (equationIdeal p hp)),
    hlen, cubicSurface_grade_two_finrank p hp hp0] at hle
  omega

theorem cubic_length_eleven_not_cohomology_one_subsingleton
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (equationIdeal p hp))
    [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (scheme (equationIdeal p hp)).Modules]
    (hlen : AllCharacteristics.finiteSchemeRank
      (i ≫ toBase (equationIdeal p hp)) = 11) :
    ¬ Subsingleton (schemeModuleCohomology (scheme (equationIdeal p hp))
      (closedImmersionIdealTwist i
        (ProjectiveNegativeTwist.positiveSheafOfModules
          (grading (equationIdeal p hp)) 2)) 1) := by
  apply cubic_finiteProjectiveClosedSubschemePositiveTwo_not_cohomology_one_subsingleton
    K p hp hp0 i
  exact cubic_length_eleven_positiveTwoRestriction_not_surjective p hp hp0 i hlen

end PfaffianDescent.ProjectiveNegativeTwist
