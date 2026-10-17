import PfaffianDescent.FieldPointExtCoordinate

/-!
# Quotient presentation of a locally trivial twisted field point

The closed-point stalk map has maximal-ideal kernel. Tensor triviality near
the point therefore identifies the twisted stalk with the quotient by any
pair of generators of that maximal ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The quotient-stalk identification for an actual twisted field point is
constructed from a local twist trivialization and the maximal-ideal span. -/
noncomputable def fieldPointPushforwardTwistStalkQuotientIsoOfLocalTrivialization
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    (T : X.Modules) (U : X.Opens) (hx : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (f g : X.presheaf.stalk (i x))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) :
    (schemeModuleStalkModuleFunctor X (i x)).obj
        (closedImmersionIdealTwistSequence i T).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)) := by
  let M : X.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI := schemeModuleStalkModule M (i x)
  let e := closedImmersionPushforwardStalkQuotientLinearEquivOfKernelEq
    i (i x) f g
    ((closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x).trans
      hspan.symm)
  exact schemeModuleTensorStalkModuleIsoOfLocalTrivialization U ⟨i x, hx⟩ M T eT ≪≫
    LinearEquiv.toModuleIso e.symm

end PfaffianDescent
