import PfaffianDescent.IdealSheafModule

/-!
# The two presentations of scheme modules

Mathlib presents sheaves of modules on a scheme both as the underlying
`SheafOfModules X.ringCatSheaf` category and as `X.Modules`, whose morphisms
are definitionally the same but which carries a separately declared category
instance.  This file gives their identity equivalence explicitly.  It lets the
closed-immersion ideal sequence, naturally stated using `X.Modules` because
of the scheme pushforward functor, be used in the sheaf category in which the
Serre extension package is formulated.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SchemeModuleBridge

variable (X : Scheme.{u})

/-- View a scheme module in the underlying category of sheaves of modules. -/
noncomputable def toSheafOfModules : X.Modules ⥤ SheafOfModules X.ringCatSheaf where
  obj M := M
  map f := f

instance : (toSheafOfModules X).PreservesZeroMorphisms where
  map_zero := by
    intros
    rfl

/-- Regard a sheaf of modules as a scheme module. -/
noncomputable def toSchemeModules : SheafOfModules X.ringCatSheaf ⥤ X.Modules where
  obj M := M
  map f := f

instance : (toSchemeModules X).PreservesZeroMorphisms where
  map_zero := by
    intros
    rfl

/-- The two category presentations of modules on a scheme are identically
equivalent.  Making the equivalence explicit transfers exact sequences across
the two category instances. -/
noncomputable def equiv : X.Modules ≌ SheafOfModules X.ringCatSheaf where
  functor := toSheafOfModules X
  inverse := toSchemeModules X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

noncomputable instance : (toSheafOfModules X).IsEquivalence :=
  (equiv X).isEquivalence_functor

noncomputable instance : (toSchemeModules X).IsEquivalence :=
  (equiv X).symm.isEquivalence_functor

/-- The actual closed-immersion ideal sequence, transported to the underlying
sheaf-of-modules category used for Serre extensions. -/
noncomputable def closedImmersionIdealSequence {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ShortComplex (SheafOfModules X.ringCatSheaf) :=
  (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).map
    (toSheafOfModules X)

@[simp]
theorem closedImmersionIdealSequence_f {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealSequence X i).f =
      IdealSheafDataModule.closedImmersionModuleToUnit i := rfl

@[simp]
theorem closedImmersionIdealSequence_g {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealSequence X i).g =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i := rfl

/-- The transported ideal sequence is short exact.  Hence the actual
closed-immersion ideal module and quotient are available in precisely the
category used by `SerreExtensionData`. -/
theorem closedImmersionIdealSequence_shortExact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealSequence X i).ShortExact := by
  apply ShortComplex.ShortExact.map_of_exact
  exact IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i

end SchemeModuleBridge
end PfaffianDescent
