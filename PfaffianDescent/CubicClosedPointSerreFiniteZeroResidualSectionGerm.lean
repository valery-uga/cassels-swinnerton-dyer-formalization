import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoordinateStalk
import PfaffianDescent.SchemeModuleLocalIsoGerm

/-! # The canonical native stalk section is the germ of the actual section -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_unit_hom_stalk_germ
    {X : Scheme.{u}} (E : X.Modules)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ E)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    (schemeModuleStalkModuleFunctor X x).map m ((schemeModuleUnitStalkIso X x).inv 1) =
      E.presheaf.germ U x hx
        (m.val.app (Opposite.op U) (1 : Γ(X, U))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hu : (schemeModuleUnitStalkIso X x).inv 1 =
      O.presheaf.germ U x hx (1 : Γ(X, U)) := by
    change presheafOfModules_unitStalkLinearEquiv X.presheaf x 1 = _
    have h := presheafOfModules_unitStalkAddEquiv_germ X.presheaf x U hx (1 : Γ(X, U))
    rw [map_one] at h
    exact h
  rw [hu]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := X.toTopCat) (C := AddCommGrpCat.{u})
    U x hx ((Scheme.Modules.toPresheaf X).map m) (1 : Γ(X, U))

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_stalk_eq_germ
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    serreExtensionStalkCanonicalSection e.toSequenceData x 1 =
      (show X.Modules from e.E).presheaf.germ U x hx
        (e.canonicalSection.val (Opposite.op U)) := by
  have h := cubicClosedPointSerreFiniteZeroResidual_unit_hom_stalk_germ e.E e.inclusion U x hx
  have hs : e.canonicalSection.val (Opposite.op U) =
      e.inclusion.val.app (Opposite.op U) (1 : Γ(X, U)) := by
    rfl
  rw [hs]
  exact h

end PfaffianDescent
