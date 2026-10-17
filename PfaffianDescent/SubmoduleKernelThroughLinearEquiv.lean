import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Equiv.Basic

/- SOURCE ONLY / UNVERIFIED. Pure linear algebra wiring; the geometric
caller proves containment and exact membership internally. -/
noncomputable section
namespace PfaffianDescent
universe u
variable {K M N A : Type u} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup A] [Module K A]

def submoduleKernelThroughLinearEquiv
    (W V : Submodule K M) (E : N ≃ₗ[K] V) (t : N →ₗ[K] A)
    (hWV : W ≤ V) (ht : ∀ s : N, (E s).val ∈ W ↔ t s = 0) :
    W ≃ₗ[K] LinearMap.ker t where
  toFun w := ⟨E.symm ⟨w.val, hWV w.property⟩,
    (ht _).mp (by simpa only [LinearEquiv.apply_symm_apply] using w.property)⟩
  invFun s := ⟨(E s.val).val, (ht s.val).mpr s.property⟩
  left_inv w := by
    apply Subtype.ext
    exact congrArg (fun z : V => z.val) (E.apply_symm_apply _)
  right_inv s := by
    apply Subtype.ext
    exact E.symm_apply_apply s.val
  map_add' w z := by
    apply Subtype.ext
    change E.symm (⟨w.val, hWV w.property⟩ + ⟨z.val, hWV z.property⟩) = _
    exact E.symm.map_add _ _
  map_smul' c w := by
    apply Subtype.ext
    change E.symm (c • (⟨w.val, hWV w.property⟩ : V)) = _
    exact E.symm.map_smul c _

end PfaffianDescent
