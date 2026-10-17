import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSelfOverlap
import PfaffianDescent.ProjectivePositiveHomogeneousChartWholeTransition

/-! The actual self-transition equals its actual overlap inclusion in
the ORIGINAL slice. The entire ambient ideal matching and native315
injection derive this identity for THIS classifier, without inverse,
reciprocal-factor or gluing assumptions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

/-- On the actual self-overlap, the constructed transition is exactly the
actual inclusion into THIS same representer. The domains are the literal
self-overlap tests; no identification of distinct chosen models is assumed. -/
theorem relativeOpenChartParameterSelfTransition_eq_inclusion001
    {X B : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (n : ℕ) [IsSeparated F]
    (H : Over B)
    (eta : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj H) :
    relativeOpenChartParameterOverlapTransition001 F U U n H H eta eta =
      relativeOpenChartParameterOverlapInclusion001 F U U n H eta := by
  let T := relativeOpenChartParameterOverlapTest001 F U U n H eta
  let t : T ⟶ H := relativeOpenChartParameterOverlapTransition001 F U U n H H eta eta
  let i : T ⟶ H := relativeOpenChartParameterOverlapInclusion001 F U U n H eta
  have hAmbient : relativeOpenChartClassifiedAmbientPoint001 F U n H eta T t =
      relativeOpenChartClassifiedAmbientPoint001 F U n H eta T i := by
    apply Subtype.ext
    exact (relativeOpenFiniteFlatPointPush_wholeIdeal315 U F n T
      (eta.inv.app (.op T) t)).trans
        (relativeOpenChartParameterOverlapTransition_wholeAmbientIdeal001
          F U U n H H eta eta)
  have hInverse : eta.inv.app (.op T) t = eta.inv.app (.op T) i :=
    relativeOpenFiniteFlatPointPush_injective315 U F n T hAmbient
  have ht : eta.hom.app (.op T) (eta.inv.app (.op T) t) = t :=
    ConcreteCategory.congr_hom (eta.inv_hom_id_app (.op T)) t
  have hi : eta.hom.app (.op T) (eta.inv.app (.op T) i) = i :=
    ConcreteCategory.congr_hom (eta.inv_hom_id_app (.op T)) i
  exact ht.symm.trans ((congrArg (fun Q => eta.hom.app (.op T) Q) hInverse).trans hi)

end PfaffianDescent
end
