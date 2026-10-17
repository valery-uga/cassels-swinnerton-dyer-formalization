import PfaffianDescent.SchemeModuleInternalHomUnitMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! The canonical unit-to-dual map has ORIGINAL chart coefficient equal
to the SAME input inclusion's value on the actual frame. A monic input
inclusion makes that actual coefficient regular. No regular-coefficient
or multiplication certificate is assumed. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- Actual dual-chart coordinate: evaluate the ACTUAL dual section on
the actual frame e^{-1}(1). Scalar action remains the original Γ(X,U). -/
def dualCoefficientLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dual M).val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U) := by
  let q := overTopLinearEquiv M U e
  let a₀ := localUnitSection M U e
  let F : (dual M).val.obj (op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U (q.symm 1)
  let G : Γ(X, U) →ₗ[Γ(X, U)] (dual M).val.obj (op U) :=
    { toFun := fun r => r • a₀
      map_add' := fun r s => add_smul r s _
      map_smul' := fun r s => mul_smul r s _ }
  apply LinearEquiv.ofLinearMap F G
  · apply LinearMap.ext
    intro r
    change F (r • a₀) = r
    rw [F.map_smul]
    change r * q (q.symm 1) = r
    rw [q.apply_symm_apply, mul_one]
  · apply LinearMap.ext
    intro a
    exact (section_eq_coefficient_smul M U e a).symm

/-- The chart coordinate is the literal value of the actual section. -/
theorem dualCoefficientLinearEquiv_apply (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (dual M).val.obj (op U)) :
    dualCoefficientLinearEquiv U e a =
      a.1.app (op (Over.mk (𝟙 U))) ((overTopLinearEquiv M U e).symm 1) := rfl

/-- The canonical map becomes multiplication by the SAME original
inclusion's actual frame value; no substitute local map is introduced. -/
theorem unitToHom_coefficient
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) (r : Γ(X, U)) :
    dualCoefficientLinearEquiv U e ((unitToHom j).val.app (op U) r) =
      @HMul.hMul (Γ(X, U)) (Γ(X, U)) (Γ(X, U)) inferInstance
        r (j.val.app (op U) ((overTopLinearEquiv M U e).symm 1)) := by
  calc
    _ = dualCoefficientLinearEquiv U e (r • homSection j U) := rfl
    _ = r • dualCoefficientLinearEquiv U e (homSection j U) :=
      (dualCoefficientLinearEquiv U e).map_smul r _
    _ = _ := rfl

/-- Monicity of the SAME original input gives injectivity of its ACTUAL
section component; the native sheaf evaluation preserves finite limits. -/
theorem inclusion_app_injective
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j] (U : X.Opens) :
    Function.Injective (j.val.app (op U)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  haveI : Mono (E.map j) := Functor.map_mono E j
  exact (ModuleCat.mono_iff_injective (E.map j)).mp (by infer_instance)

/-- The actual frame image is regular, derived from the SAME monic
inclusion and genuine unit chart. This is not a regularity premise. -/
theorem inclusion_frame_isRegular
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j] (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    @IsRegular (Γ(X, U)) inferInstance
      (j.val.app (op U) ((overTopLinearEquiv M U e).symm 1)) := by
  let q := overTopLinearEquiv M U e
  let z : Γ(X, U) := j.val.app (op U) (q.symm 1)
  have hmul (r : Γ(X, U)) : j.val.app (op U) (q.symm r) = r * z := by
    calc
      _ = j.val.app (op U) (r • q.symm 1) := by
        rw [← q.symm.map_smul, smul_eq_mul, mul_one]
      _ = r • (j.val.app (op U) (q.symm 1) : Γ(X, U)) :=
        (j.val.app (op U)).hom.map_smul r _
      _ = r * z := rfl
  have hright : Function.Injective (fun r : Γ(X, U) => r * z) := by
    intro r s h
    apply q.symm.injective
    apply inclusion_app_injective j U
    rw [hmul, hmul]
    exact h
  exact ⟨fun r s h => hright ((mul_comm r z).trans (h.trans (mul_comm z s))), hright⟩

/-- Actual canonical increment is injective on a genuine unit chart,
using internally derived regularity of its ACTUAL coefficient. -/
theorem unitToHom_app_injective
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j] (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Injective ((unitToHom j).val.app (op U)) := by
  intro r s h
  have h' := congrArg (dualCoefficientLinearEquiv U e) h
  rw [unitToHom_coefficient, unitToHom_coefficient] at h'
  exact (inclusion_frame_isRegular j U e).right h'

end PfaffianDescent.SchemeModuleInternalHom
