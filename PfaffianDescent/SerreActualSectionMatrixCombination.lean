import PfaffianDescent.SchemeModuleParameterizedSection
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Matrix coordinate changes for genuine sections, with regular-function
coefficients on the whole scheme. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem serreActualFiniteCombination_matrix
    {X : Scheme.{u}} {M : X.Modules}
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ Γ(X, ⊤)) (c : κ → Γ(X, ⊤)) (s : ι → M.sections) :
    finiteLinearCombinationSections
        (fun k => unitEndomorphismOfRegularFunction (c k))
        (fun k => finiteLinearCombinationSections
          (fun i => unitEndomorphismOfRegularFunction (A i k)) s) =
      finiteLinearCombinationSections
        (fun i => unitEndomorphismOfRegularFunction ((A.mulVec c) i)) s := by
  let θ : Γ(X, ⊤) →+ (schemeModuleUnit X ⟶ schemeModuleUnit X) :=
    { toFun := unitEndomorphismOfRegularFunction
      map_zero' := unitEndomorphismOfRegularFunction_zero
      map_add' := unitEndomorphismOfRegularFunction_add }
  apply M.unitHomEquiv.symm.injective
  simp only [finiteLinearCombinationSections, sumSections_unitHomEquiv_symm,
    scaleSection, Equiv.symm_apply_apply]
  change (∑ k, θ (c k) ≫ ∑ i, θ (A i k) ≫ M.unitHomEquiv.symm (s i)) =
    ∑ i, θ ((A.mulVec c) i) ≫ M.unitHomEquiv.symm (s i)
  simp_rw [Preadditive.comp_sum, ← Category.assoc]
  have hm (k : κ) (i : ι) : θ (c k) ≫ θ (A i k) = θ (A i k * c k) := by
    change unitEndomorphismOfRegularFunction (c k) ≫
        unitEndomorphismOfRegularFunction (A i k) =
      unitEndomorphismOfRegularFunction (A i k * c k)
    rw [mul_comm, unitEndomorphismOfRegularFunction_mul]
  simp_rw [hm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ k, θ (A i k * c k) ≫ M.unitHomEquiv.symm (s i)) =
    θ (∑ k, A i k * c k) ≫ M.unitHomEquiv.symm (s i)
  rw [map_sum, Preadditive.sum_comp]

end PfaffianDescent
