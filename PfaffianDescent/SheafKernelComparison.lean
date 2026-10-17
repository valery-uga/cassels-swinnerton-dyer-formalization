import PfaffianDescent.SheafKernelSections

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe u v w
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N P : SheafOfModules.{u} R} (f : M ⟶ N) (g : M ⟶ P)

lemma sheafKernelConditionOfSections
    (h : ∀ U, (f.val.app U).hom.ker ≤ (g.val.app U).hom.ker) :
    kernel.ι f ≫ g = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := CategoryTheory.congr_fun
    (congrArg (fun q : kernel f ⟶ N => q.val.app U) (kernel.condition f)) x
  change f.val.app U ((kernel.ι f).val.app U x) = 0 at hx
  exact h U hx

/-- Inclusion of section kernels gives the actual comparison of kernel sheaves. -/
noncomputable def sheafKernelComparisonOfSections
    (h : ∀ U, (f.val.app U).hom.ker ≤ (g.val.app U).hom.ker) : kernel f ⟶ kernel g :=
  kernel.lift g (kernel.ι f) (sheafKernelConditionOfSections R f g h)

lemma sheafKernelComparisonOfSections_ι
    (h : ∀ U, (f.val.app U).hom.ker ≤ (g.val.app U).hom.ker) :
    sheafKernelComparisonOfSections R f g h ≫ kernel.ι g = kernel.ι f :=
  kernel.lift_ι _ _ _

/-- Equal concrete kernels on every open identify the actual kernel sheaves. -/
noncomputable def sheafKernelIsoOfEqualSections
    (h : ∀ U, (f.val.app U).hom.ker = (g.val.app U).hom.ker) : kernel f ≅ kernel g where
  hom := sheafKernelComparisonOfSections R f g (fun U => (h U).le)
  inv := sheafKernelComparisonOfSections R g f (fun U => (h U).ge)
  hom_inv_id := by
    apply equalizer.hom_ext
    rw [Category.assoc, sheafKernelComparisonOfSections_ι, sheafKernelComparisonOfSections_ι, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    rw [Category.assoc, sheafKernelComparisonOfSections_ι, sheafKernelComparisonOfSections_ι, Category.id_comp]

lemma sheafKernelIsoOfEqualSections_hom_ι
    (h : ∀ U, (f.val.app U).hom.ker = (g.val.app U).hom.ker) :
    (sheafKernelIsoOfEqualSections R f g h).hom ≫ kernel.ι g = kernel.ι f :=
  sheafKernelComparisonOfSections_ι R f g (fun U => (h U).le)

end
end PfaffianDescent
