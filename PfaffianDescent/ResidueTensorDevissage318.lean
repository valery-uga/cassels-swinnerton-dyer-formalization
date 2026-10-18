import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
The two diagram-chase steps in Artin-base flatness
devissage. Neither injectivity upstairs nor flatness of a new quotient is
assumed.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
universe u v w t

/-- Residue injectivity remains injective after tensoring with any module
over the residue field, by actual scalar-cancellation equivalences. -/
theorem lTensor_injective_of_residueModule318
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    {F : Type v} {N : Type w} [AddCommGroup F] [AddCommGroup N]
    [Module R F] [Module R N] (f : F →ₗ[R] N)
    (hred : Function.Injective (f.lTensor (R ⧸ I)))
    (T : Type t) [AddCommGroup T] [Module R T]
    [Module (R ⧸ I) T] [IsScalarTower R (R ⧸ I) T] :
    Function.Injective (f.lTensor T) := by
  let k := R ⧸ I
  letI : Field k := Ideal.Quotient.field I
  let eF := AlgebraTensorModule.cancelBaseChange R k k T F
  let eN := AlgebraTensorModule.cancelBaseChange R k k T N
  have hred' : Function.Injective (f.baseChange k) := hred
  have ht : Function.Injective ((f.baseChange k).lTensor T) :=
    Module.Flat.lTensor_preserves_injective_linearMap (f.baseChange k) hred'
  have hcomm : (f.lTensor T).comp (eF.toLinearMap.restrictScalars R) =
      (eN.toLinearMap.restrictScalars R).comp
        (((f.baseChange k).lTensor T).restrictScalars R) := by
    apply LinearMap.ext
    intro z
    change f.lTensor T (eF z) = eN (((f.baseChange k).lTensor T) z)
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul a y => rfl
      | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hx' : ((f.baseChange k).lTensor T) (eF.symm x) = 0 := by
    apply (injective_iff_map_eq_zero _).mp eN.injective
    have h := congrArg (fun g : T ⊗[k] (k ⊗[R] F) →ₗ[R] T ⊗[R] N =>
      g (eF.symm x)) hcomm
    have hh : eN (((f.baseChange k).lTensor T) (eF.symm x)) = f.lTensor T x := by
      change f.lTensor T (eF (eF.symm x)) =
        eN (((f.baseChange k).lTensor T) (eF.symm x)) at h
      rw [eF.apply_symm_apply] at h
      exact h.symm
    exact hh.trans hx
  have hzero : eF.symm x = 0 := (injective_iff_map_eq_zero _).mp ht _ hx'
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg eF hzero

/-- Injectivity after tensoring passes across a short exact sequence of
test modules when both modules in the map under test are flat. -/
theorem lTensor_injective_of_extension318
    {R : Type u} [CommRing R]
    {F : Type v} {N : Type w} [AddCommGroup F] [AddCommGroup N]
    [Module R F] [Module R N] [Module.Flat R F] [Module.Flat R N]
    (f : F →ₗ[R] N)
    {T₁ T₂ T₃ : Type t}
    [AddCommGroup T₁] [AddCommGroup T₂] [AddCommGroup T₃]
    [Module R T₁] [Module R T₂] [Module R T₃]
    (g : T₁ →ₗ[R] T₂) (q : T₂ →ₗ[R] T₃)
    (hg : Function.Injective g) (hq : Function.Surjective q)
    (hex : Function.Exact g q)
    (h₁ : Function.Injective (f.lTensor T₁))
    (h₃ : Function.Injective (f.lTensor T₃)) :
    Function.Injective (f.lTensor T₂) := by
  have hqcomm : (f.lTensor T₃).comp (q.rTensor F) =
      (q.rTensor N).comp (f.lTensor T₂) := by ext x y; rfl
  have hgcomm : (f.lTensor T₂).comp (g.rTensor F) =
      (g.rTensor N).comp (f.lTensor T₁) := by ext x y; rfl
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hqx : q.rTensor F x = 0 := by
    apply (injective_iff_map_eq_zero _).mp h₃
    change ((f.lTensor T₃).comp (q.rTensor F)) x = 0
    rw [hqcomm, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨y, hy⟩ := (Module.Flat.rTensor_exact F hex x).mp hqx
  have hfy : f.lTensor T₁ y = 0 := by
    apply (injective_iff_map_eq_zero _).mp
      (Module.Flat.rTensor_preserves_injective_linearMap g hg (M := N))
    change ((g.rTensor N).comp (f.lTensor T₁)) y = 0
    rw [← hgcomm, LinearMap.comp_apply, hy, hx]
  have hyzero : y = 0 := (injective_iff_map_eq_zero _).mp h₁ y hfy
  rw [← hy, hyzero, map_zero]

end AllCharacteristics
end
