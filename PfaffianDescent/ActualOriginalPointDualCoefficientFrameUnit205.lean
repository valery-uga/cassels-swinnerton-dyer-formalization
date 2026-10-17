import PfaffianDescent.SchemeModuleActualDualIncrementStalkPrincipal194
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! SOURCE ONLY205. Actual original ideal frames differ by a local-ring unit.
Its original residue compares194's coefficient with191's actual chart.
No differential normalization or coefficient-comparison premise is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeModuleInternalHom IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A linear automorphism of the literal rank-one ring has a unit value at one. -/
theorem originalRingLinearEquiv_one_isUnit205
    {R : Type u} [CommRing R] (e : R ≃ₗ[R] R) : IsUnit (e 1) := by
  have hv (r : R) : e r = r * e 1 := by
    calc
      e r = e (r • (1 : R)) := by simp only [smul_eq_mul, mul_one]
      _ = r • e 1 := e.map_smul r 1
      _ = r * e 1 := rfl
  apply isUnit_iff_exists_inv.mpr
  refine ⟨e.symm 1, ?_⟩
  rw [mul_comm]
  exact (hv (e.symm 1)).symm.trans (e.apply_symm_apply 1)

/-- SAME original local-ring unit comparing the given ideal frame to its
actual over-site chart. Both maps are independently original linear maps. -/
def actualOriginalIdealFrameUnit205
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M)) :
    X.presheaf.stalk (U.ι x) :=
  (originalIdealFrameNativeStalkIso191 U x M e).hom (e₀ 1)

theorem actualOriginalIdealFrameUnit_isUnit205
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M)) :
    IsUnit (actualOriginalIdealFrameUnit205 U x M e e₀) :=
  originalRingLinearEquiv_one_isUnit205
    (e₀.trans (originalIdealFrameNativeStalkIso191 U x M e).toLinearEquiv)

/-- The literal194 coefficient is the chart coefficient times that DERIVED
unit. This retains the whole original dual stalk and its actual evaluation. -/
theorem actualDualIncrementStalkCoefficient_frameUnit205
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M)) :
    (actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom a =
      actualOriginalIdealFrameUnit205 U x M e e₀ *
        (actualDualFrameNativeStalkIso191 U x M e).hom a := by
  change actualDualNativeStalkLinearEquiv191 U x M e a (e₀ 1) = _
  exact actualDualNativeStalkLinearEquiv_apply191 U x M e a (e₀ 1)

/-- Original residue of the genuine original frame unit remains a unit. -/
theorem actualOriginalIdealFrameResidue_isUnit205
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M)) :
    IsUnit (residue (X.presheaf.stalk (U.ι x))
      (actualOriginalIdealFrameUnit205 U x M e e₀)) :=
  (actualOriginalIdealFrameUnit_isUnit205 U x M e e₀).map
    (residue (X.presheaf.stalk (U.ι x)))

/-- Exact original residue coefficient; no scalar action is transported
through a chosen quotient Iso.194's projection law can be applied first. -/
theorem actualDualIncrementStalkCoefficient_residue_frameUnit205
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (e₀ : X.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M))
    (a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M)) :
    residue (X.presheaf.stalk (U.ι x))
        ((actualDualIncrementStalkCoefficientIso194 U x M e e₀).hom a) =
      residue (X.presheaf.stalk (U.ι x)) (actualOriginalIdealFrameUnit205 U x M e e₀) *
        residue (X.presheaf.stalk (U.ι x))
          ((actualDualFrameNativeStalkIso191 U x M e).hom a) := by
  rw [actualDualIncrementStalkCoefficient_frameUnit205 U x M e e₀ a]
  exact map_mul (residue (X.presheaf.stalk (U.ι x))) _ _

end PfaffianDescent
