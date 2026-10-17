import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalLift

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The categorical kernel lift is an actual global sheaf section, and its
literal inclusion is the original homogeneous cubic section. The quotient
vanishing premise is the intermediate target discharged by the chart comparison. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveCubicIdealSection_of_quotient_zero
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (q : grading I 3)
    (hq : (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q) ≫
        (schemeModuleTensorUnitLeftIso
          (positiveSheafOfModules (grading I) 3)).inv ≫
        (closedImmersionIdealTwistSequence i
          (positiveSheafOfModules (grading I) 3)).g = 0) :
    ∃ t : (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading I) 3)).sections,
      SheafOfModules.sectionsMap
        (cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I i) t =
          positiveGlobalSectionOfHomogeneous (grading I) 3 q := by
  obtain ⟨t, ht, _⟩ :=
    cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift I i _ hq
  refine ⟨(closedImmersionIdealTwist i
    (positiveSheafOfModules (grading I) 3)).unitHomEquiv t, ?_⟩
  apply (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm.injective
  rw [← SheafOfModules.unitHomEquiv_symm_comp]
  exact (congrArg
    (fun a => a ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I i)
    ((closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3)).unitHomEquiv
      |>.symm_apply_apply t)).trans ht

end PfaffianDescent
