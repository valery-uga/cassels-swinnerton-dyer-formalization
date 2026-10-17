import PfaffianDescent.CubicPointTraceFieldBaseChangeDiagonalExtZero

/-! SOURCE ONLY224. Contraposition of the actual finite-separable diagonal
zero descent. The intermediate nonzero diagonal unit input is explicit;
only the original geometry factory below may discharge it internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A nonzero actual diagonal unit restriction detects some actual original
residue-field scalar unit restriction. This helper has a nonzero intermediate
input and is not itself the original geometric nonvanishing endpoint. -/
theorem actualFiniteSeparableDiagonalUnit_exists_scalarUnitNonzero224
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (.of K))
    (i : Spec (.of L) ⟶ Y) [IsClosedImmersion i]
    (hi : i ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasExt.{u} Y.Modules]
    [HasExt.{u} (schemeBaseChangeToField (L := L) Y pi).Modules]
    (N : Y.Modules) (n : ℕ)
    (z : Ext.{u} (C := Y.Modules) ((Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n)
    (hDiagonalUnit :
      (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) Y pi).Modules)
        (closedImmersionUnitToPushforwardUnit
          (cubicPointTraceFieldBaseChangeRationalPoint K L pi i hi))).comp
        (cubicPointTraceFieldBaseChangeDiagonalExtClass K L pi i hi N n z)
        (zero_add n) ≠ 0) :
    ∃ a : L,
      (Ext.mk₀.{u} (C := Y.Modules) (closedImmersionUnitToPushforwardUnit i)).comp
        ((Ext.mk₀.{u} (C := Y.Modules)
          (fieldPointPushforwardScalarEndomorphismAddHom i a)).comp z (zero_add n))
        (zero_add n) ≠ 0 := by
  classical
  by_contra! hzero
  exact hDiagonalUnit
    (cubicPointTraceFieldBaseChangeDiagonalExtClass_unit_eq_zero K L pi i hi N n z hzero)

end PfaffianDescent
