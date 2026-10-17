import PfaffianDescent.ExtAcyclicResolutionDegreeThree
import PfaffianDescent.ExtAcyclicResolutionDegreeTwo

/-! # Coefficient connecting classes computed on a source resolution -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
namespace ThreeStepResolution

/-- The first two stages of the actual three-step source resolution. -/
def toTwoStep (R : ThreeStepResolution A) : TwoStepResolution A where
  P := R.P
  C₀ := R.C₀
  C₁ := R.C₁
  K₀ := R.K₀
  K₁ := R.K₁
  i₀ := R.i₀
  p₀ := R.p₀
  zero₀ := R.zero₀
  i₁ := R.i₁
  p₁ := R.p₁
  zero₁ := R.zero₁
  exact₀ := R.exact₀
  exact₁ := R.exact₁

/-- A lift through a coefficient extension computes its connecting class
by the coefficient induced on the next source kernel. -/
theorem prefix_connecting_comp_coefficient_extension
    (R : ThreeStepResolution A) (S : ShortComplex A) (hS : S.ShortExact)
    (φ : R.K₁ ⟶ S.X₃) (l : R.C₂ ⟶ S.X₂) (ψ : R.K₂ ⟶ S.X₁)
    (hleft : R.i₂ ≫ l = ψ ≫ S.f) (hright : R.p₂ ≫ φ = l ≫ S.g) :
    ((R.toTwoStep).connecting S.X₃ φ).comp hS.extClass (show 2 + 1 = 3 by rfl) =
      R.connecting S.X₁ ψ := by
  let f : R.S₂ ⟶ S := { τ₁ := ψ, τ₂ := l, τ₃ := φ, comm₁₂ := hleft.symm, comm₂₃ := hright.symm }
  have hnat := R.exact₂.extClass_naturality hS f
  change R.exact₂.extClass.comp (Ext.mk₀ ψ) (add_zero 1) =
    (Ext.mk₀ φ).comp hS.extClass (zero_add 1) at hnat
  change (R.exact₀.extClass.comp
    (R.exact₁.extClass.comp (Ext.mk₀ φ) (add_zero 1)) (show 1 + 1 = 2 by rfl)).comp
      hS.extClass (show 2 + 1 = 3 by rfl) = _
  rw [Ext.comp_assoc _ _ _ rfl rfl rfl,
    Ext.comp_assoc_of_second_deg_zero _ _ _ rfl, ← hnat]
  rfl
end ThreeStepResolution
end PfaffianDescent
