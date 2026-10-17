import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe u v w
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R} (f : M ⟶ N) (U : Cᵒᵖ)

instance sheafEvaluation_preservesZeroMorphisms :
    (SheafOfModules.evaluation.{u} R U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Sections of an actual kernel sheaf are the concrete kernel of the map on sections. -/
noncomputable def sheafKernelSectionsIso :
    (kernel f).val.obj U ≅ ModuleCat.of (R.obj.obj U) (f.val.app U).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation.{u} R U) f ≪≫
    ModuleCat.kernelIsoKer (f.val.app U)

lemma sheafKernelSectionsIso_subtype :
    (sheafKernelSectionsIso R f U).hom ≫ ModuleCat.ofHom (f.val.app U).hom.ker.subtype =
      (kernel.ι f).val.app U := by
  change ((PreservesKernel.iso (SheafOfModules.evaluation.{u} R U) f).hom ≫
    (ModuleCat.kernelIsoKer ((SheafOfModules.evaluation.{u} R U).map f)).hom) ≫
      ModuleCat.ofHom ((SheafOfModules.evaluation.{u} R U).map f).hom.ker.subtype =
        (SheafOfModules.evaluation.{u} R U).map (kernel.ι f)
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι f (SheafOfModules.evaluation.{u} R U)

end
end PfaffianDescent
