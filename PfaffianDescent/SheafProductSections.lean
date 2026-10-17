import PfaffianDescent.SheafKernelSections
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe u v w
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {ι : Type} (N : ι → SheafOfModules.{u} R) (U : Cᵒᵖ)

/-- Sections of a product sheaf are tuples of sections of the factors. -/
noncomputable def sheafProductSectionsIso :
    (∏ᶜ N).val.obj U ≅ ModuleCat.of (R.obj.obj U) (∀ i, (N i).val.obj U) :=
  PreservesProduct.iso (SheafOfModules.evaluation.{u} R U) N ≪≫
    ModuleCat.piIsoPi (fun i => (N i).val.obj U)

lemma sheafProductSectionsIso_projection (i : ι) :
    (sheafProductSectionsIso R N U).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (Pi.π N i).val.app U := by
  change ((PreservesProduct.iso (SheafOfModules.evaluation.{u} R U) N).hom ≫
    (ModuleCat.piIsoPi (fun i => (SheafOfModules.evaluation.{u} R U).obj (N i))).hom) ≫
      ModuleCat.ofHom (LinearMap.proj i) = (SheafOfModules.evaluation.{u} R U).map (Pi.π N i)
  rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom]
  exact piComparison_comp_π (SheafOfModules.evaluation.{u} R U) N i

lemma sheafProductSectionsIso_apply (x : (∏ᶜ N).val.obj U) (i : ι) :
    (sheafProductSectionsIso R N U).hom x i = (Pi.π N i).val.app U x :=
  CategoryTheory.congr_fun (sheafProductSectionsIso_projection R N U i) x

lemma sheafProductSections_zero_iff (x : (∏ᶜ N).val.obj U) :
    x = 0 ↔ ∀ i, (Pi.π N i).val.app U x = 0 := by
  constructor
  · rintro rfl i
    exact map_zero _
  · intro h
    apply (sheafProductSectionsIso R N U).toLinearEquiv.injective
    change (sheafProductSectionsIso R N U).hom x = (sheafProductSectionsIso R N U).hom 0
    rw [map_zero]
    funext i
    exact (sheafProductSectionsIso_apply R N U x i).trans (h i)

lemma sheafProductSections_lift_zero_iff {M : SheafOfModules.{u} R} (f : ∀ i, M ⟶ N i)
    (x : M.val.obj U) :
    (Pi.lift f).val.app U x = 0 ↔ ∀ i, (f i).val.app U x = 0 := by
  rw [sheafProductSections_zero_iff R N U]
  apply forall_congr'
  intro i
  have h := CategoryTheory.congr_fun
    (congrArg (fun g : M ⟶ N i => g.val.app U) (Pi.lift_π f i)) x
  change (Pi.π N i).val.app U ((Pi.lift f).val.app U x) = (f i).val.app U x at h
  rw [h]

/-- The simultaneous concrete kernel of a family of sheaf morphisms on sections. -/
noncomputable def simultaneousSheafKernel {M : SheafOfModules.{u} R} (f : ∀ i, M ⟶ N i) :
    Submodule (R.obj.obj U) (M.val.obj U) :=
  ⨅ i, ((f i).val.app U).hom.ker

lemma mem_simultaneousSheafKernel {M : SheafOfModules.{u} R} (f : ∀ i, M ⟶ N i)
    (x : M.val.obj U) : x ∈ simultaneousSheafKernel R N U f ↔ ∀ i, (f i).val.app U x = 0 := by
  simp only [simultaneousSheafKernel, Submodule.mem_iInf, LinearMap.mem_ker]

lemma sheafProductSections_kernel {M : SheafOfModules.{u} R} (f : ∀ i, M ⟶ N i) :
    ((Pi.lift f).val.app U).hom.ker = simultaneousSheafKernel R N U f := by
  ext x
  rw [mem_simultaneousSheafKernel]
  exact sheafProductSections_lift_zero_iff R N U f x

/-- Sections of a simultaneous kernel sheaf are its simultaneous concrete kernel. -/
noncomputable def sheafSimultaneousKernelSectionsEquiv {M : SheafOfModules.{u} R}
    (f : ∀ i, M ⟶ N i) :
    (kernel (Pi.lift f)).val.obj U ≃ₗ[R.obj.obj U] simultaneousSheafKernel R N U f :=
  (sheafKernelSectionsIso R (Pi.lift f) U).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (sheafProductSections_kernel R N U f))

lemma sheafSimultaneousKernelSectionsEquiv_val {M : SheafOfModules.{u} R}
    (f : ∀ i, M ⟶ N i) (x : (kernel (Pi.lift f)).val.obj U) :
    (sheafSimultaneousKernelSectionsEquiv R N U f x).1 =
      (kernel.ι (Pi.lift f)).val.app U x :=
  CategoryTheory.congr_fun (sheafKernelSectionsIso_subtype R (Pi.lift f) U) x

end
end PfaffianDescent
