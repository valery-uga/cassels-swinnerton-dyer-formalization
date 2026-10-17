import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSelfTransition
import PfaffianDescent.ProjectivePositiveHomogeneousChartReciprocalOverlapIso

/-! The actual reciprocal self-overlap factor is the IDENTITY on its
literal original self-overlap object. The equality follows from the
constructed transition factor square, the derived self-transition law,
and cancellation of the actual open immersion. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

/-- Genuine self-identity for the actual reciprocal factor, typed in the
original slice category on the SAME self-overlap test. No identity,
inverse, compatibility, or gluing conclusion is supplied as a premise. -/
theorem relativeOpenChartParameterSelfReciprocalMap_eq_id001
    {X B : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (n : ℕ) [IsSeparated F]
    (H : Over B)
    (eta : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj H) :
    relativeOpenChartParameterOverlapReciprocalMap001 F U U n H H eta eta =
      𝟙 (relativeOpenChartParameterOverlapTest001 F U U n H eta) := by
  let i := relativeOpenChartParameterOverlapInclusion001 F U U n H eta
  have hi : relativeOpenChartParameterOverlapReciprocalMap001 F U U n H H eta eta ≫ i = i :=
    (relativeOpenChartParameterOverlapReciprocalMap_comp001 F U U n H H eta eta).trans
      (relativeOpenChartParameterSelfTransition_eq_inclusion001 F U n H eta)
  apply Over.OverMorphism.ext
  letI : Mono i.left := by
    change Mono (relativeOpenChartParameterOverlap001 F U U n H eta).ι
    infer_instance
  apply (cancel_mono i.left).mp
  exact (congrArg (fun f => f.left) hi).trans (Category.id_comp i.left).symm

end PfaffianDescent
end
