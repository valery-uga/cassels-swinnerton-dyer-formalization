import PfaffianDescent.SerreActualParameterizedSectionPullback
import PfaffianDescent.SerreActualSectionMatrixCombination
import Mathlib.LinearAlgebra.Matrix.Basis

/-! The actual universal linear combination is independent of the chosen
global-section basis when its regular coefficients change by the genuine
basis matrix. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem serreActualGlobalSectionsOver_sum_smul
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι] (a : ι → K)
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    schemeModuleGlobalSectionsOverEquivSections base M (∑ i, a i • s i) =
      finiteLinearCombinationSections
        (fun i => unitEndomorphismOfRegularFunction (affineFunctionHom base (a i)))
        (fun i => schemeModuleGlobalSectionsOverEquivSections base M (s i)) := by
  let M' : SheafOfModules.{u} X.ringCatSheaf := M
  apply M'.unitHomEquiv.symm.injective
  have ht (i : ι) :
      M'.unitHomEquiv.symm
        (scaleSection (unitEndomorphismOfRegularFunction (affineFunctionHom base (a i)))
          (M'.unitHomEquiv (s i))) = a i • s i := by
    change M'.unitHomEquiv.symm
        (M'.unitHomEquiv
          (unitEndomorphismOfRegularFunction (affineFunctionHom base (a i)) ≫
            M'.unitHomEquiv.symm (M'.unitHomEquiv (s i)))) = a i • s i
    rw [M'.unitHomEquiv.symm_apply_apply, M'.unitHomEquiv.symm_apply_apply]
    rfl
  change M'.unitHomEquiv.symm (M'.unitHomEquiv (∑ i, a i • s i)) =
    M'.unitHomEquiv.symm (sumSections (fun i =>
      scaleSection (unitEndomorphismOfRegularFunction (affineFunctionHom base (a i)))
        (M'.unitHomEquiv (s i))))
  rw [M'.unitHomEquiv.symm_apply_apply, sumSections_unitHomEquiv_symm]
  exact (Finset.sum_congr rfl (fun i _ => ht i)).symm

theorem serreActualParameterizedSection_basis_change
    {K : Type u} [Field K] {X U : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (b : Basis κ K (SchemeModuleGlobalSectionsOver base M))
    (c : Basis ι K (SchemeModuleGlobalSectionsOver base M))
    (f : U ⟶ X) (coeff : κ → Γ(U, ⊤)) :
    parameterizedSchemeModuleSection base M f coeff b =
      parameterizedSchemeModuleSection base M f
        (((c.toMatrix b).map (affineFunctionHom (f ≫ base))).mulVec coeff) c := by
  let A := (c.toMatrix b).map (affineFunctionHom (f ≫ base))
  have hb (k : κ) :
      schemeModuleGlobalSectionsOverEquivSections base M (b k) =
        finiteLinearCombinationSections
          (fun i => unitEndomorphismOfRegularFunction
            (affineFunctionHom base (c.toMatrix b i k)))
          (fun i => schemeModuleGlobalSectionsOverEquivSections base M (c i)) := by
    have h := serreActualGlobalSectionsOver_sum_smul base M
      (fun i => c.repr (b k) i) c
    rw [c.sum_repr] at h
    exact h
  have hpb (k : κ) :
      pullbackSection f M (isIso_pullbackUnitComparison f)
        (schemeModuleGlobalSectionsOverEquivSections base M (b k)) =
      finiteLinearCombinationSections
        (fun i => unitEndomorphismOfRegularFunction (A i k))
        (fun i => pullbackSection f M (isIso_pullbackUnitComparison f)
          (schemeModuleGlobalSectionsOverEquivSections base M (c i))) := by
    rw [hb k, serreActualFiniteCombination_pullback]
    congr 1
  unfold parameterizedSchemeModuleSection
  have hs := funext hpb
  rw [hs]
  exact serreActualFiniteCombination_matrix A coeff _

end PfaffianDescent
