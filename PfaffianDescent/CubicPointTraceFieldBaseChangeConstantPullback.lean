import PfaffianDescent.CubicPointTraceFieldBaseChangeClosedSupport
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! # Actual pullback of multiplication by regular functions -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PfaffianDescent.BundleSectionZeroLocus
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual structure-module restriction intertwines multiplication by
a global regular function and by its actual pullback. -/
theorem cubicPointTraceFieldBaseChange_unitPushforward_regularFunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    unitEndomorphismOfRegularFunction r ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f =
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f ≫
      (Scheme.Modules.pushforward f).map
        (unitEndomorphismOfRegularFunction (f.appTop r)) := by
  let M := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  apply (M.unitHomEquiv.trans (schemeModuleSectionsEquivTop M)).injective
  change (f.appTop).hom
      (unitEndomorphismValue (unitEndomorphismOfRegularFunction r)) =
    ((unitEndomorphismOfRegularFunction (f.appTop r)).val.app (Opposite.op ⊤)).hom
      ((f.appTop).hom 1)
  rw [unitEndomorphismValue_ofRegularFunction, map_one]
  exact (unitEndomorphismValue_ofRegularFunction (f.appTop r)).symm

/-- Actual geometric pullback intertwines regular-function multiplication
under the canonical unit comparison, for arbitrary scheme morphisms. -/
theorem cubicPointTraceFieldBaseChange_pullbackUnit_regularFunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (unitEndomorphismOfRegularFunction r) ≫
      pullbackUnitComparison f =
    pullbackUnitComparison f ≫ unitEndomorphismOfRegularFunction (f.appTop r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have h := congrArg
    (fun t : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) =>
        (adj.homEquiv _ _).symm t)
    (cubicPointTraceFieldBaseChange_unitPushforward_regularFunction f r)
  rw [adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm] at h
  exact h

/-- Constants on the original point become the actual constants defined
by its scalar-extension projection. -/
theorem cubicPointTraceFieldBaseChange_pullbackUnit_constant
    {L : Type u} [Field L] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of L)) (a : L) :
    (Scheme.Modules.pullback f).map (schemeModuleConstantEndomorphism p a) ≫
      pullbackUnitComparison f =
    pullbackUnitComparison f ≫ schemeModuleConstantEndomorphism (f ≫ p) a := by
  unfold schemeModuleConstantEndomorphism
  rw [affineFunctionHom_comp]
  exact cubicPointTraceFieldBaseChange_pullbackUnit_regularFunction f (affineFunctionHom p a)

end PfaffianDescent
