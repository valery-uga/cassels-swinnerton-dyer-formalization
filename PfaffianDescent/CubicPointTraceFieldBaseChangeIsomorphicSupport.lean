import PfaffianDescent.CubicPointTraceFieldBaseChangePointSummand
import PfaffianDescent.CubicPointTraceFieldBaseChangeClosedSupport

/-! # Actual point support transported through its affine fibre isomorphism -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- For an actual scheme isomorphism the actual structure-to-pushforward
map is itself an isomorphism. -/
theorem cubicPointTraceFieldBaseChange_isIso_unitPushforward
    {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] :
    IsIso (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (f.app U).hom
  exact (asIso (f.app U)).commRingCatIsoToRingEquiv.bijective

/-- The actual support pushforward comparison for an isomorphism of support
schemes, using the actual structure-module map. -/
def cubicPointTraceFieldBaseChangeIsomorphicSupportIso
    {A B X : Scheme.{u}} (e : A ≅ B) (j : B ⟶ X) :
    (Scheme.Modules.pushforward j).obj (SheafOfModules.unit B.ringCatSheaf) ≅
      (Scheme.Modules.pushforward (e.hom ≫ j)).obj
        (SheafOfModules.unit A.ringCatSheaf) := by
  letI := cubicPointTraceFieldBaseChange_isIso_unitPushforward e.hom
  exact (Scheme.Modules.pushforward j).mapIso
      (asIso (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit e.hom)) ≪≫
    (Scheme.Modules.pushforwardComp e.hom j).app (SheafOfModules.unit A.ringCatSheaf)

/-- Transporting support by its actual isomorphism preserves the actual
ambient unit quotient. -/
theorem cubicPointTraceFieldBaseChangeIsomorphicSupportIso_unit
    {A B X : Scheme.{u}} (e : A ≅ B) (j : B ⟶ X) :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫
      (cubicPointTraceFieldBaseChangeIsomorphicSupportIso e j).hom =
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (e.hom ≫ j) := by
  exact cubicPointTraceFieldBaseChange_unitPushforward_comp e.hom j

end PfaffianDescent
