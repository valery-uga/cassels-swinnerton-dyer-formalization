import PfaffianDescent.SheafKernelSections
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe u v w
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})

/-- A sheaf morphism bijective on every module of sections is an isomorphism. -/
noncomputable def sheafIsoOfBijectiveSections {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) : M ≅ N := by
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (M₁ := M.val) (M₂ := N.val)
      (fun U => by
        haveI : IsIso (f.val.app U) := (ConcreteCategory.isIso_iff_bijective _).mpr (hf U)
        exact asIso (f.val.app U))
      (fun {U V} h => f.val.naturality h))

lemma sheafIsoOfBijectiveSections_hom {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) :
    (sheafIsoOfBijectiveSections R f hf).hom = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A morphism that gives kernel coordinates on every open gives actual sheaf kernel coordinates. -/
noncomputable def sheafKernelIsoOfSectionEquiv {M N P : SheafOfModules.{u} R}
    (f : M ⟶ N) (g : M ⟶ P)
    (e : ∀ U, (f.val.app U).hom.ker ≃ₗ[R.obj.obj U] P.val.obj U)
    (he : ∀ U c, e U c = g.val.app U c.1) : kernel f ≅ P := by
  apply sheafIsoOfBijectiveSections R (kernel.ι f ≫ g)
  intro U
  let E := (sheafKernelSectionsIso R f U).toLinearEquiv.trans (e U)
  have hE (x : (kernel f).val.obj U) : E x = (kernel.ι f ≫ g).val.app U x := by
    change e U ((sheafKernelSectionsIso R f U).toLinearEquiv x) = _
    rw [he]
    have h := CategoryTheory.congr_fun (sheafKernelSectionsIso_subtype R f U) x
    exact congrArg (g.val.app U) h
  have hh : (fun x => (kernel.ι f ≫ g).val.app U x) = E := funext (fun x => (hE x).symm)
  change Function.Bijective (fun x => (kernel.ι f ≫ g).val.app U x)
  rw [hh]
  exact E.bijective

lemma sheafKernelIsoOfSectionEquiv_hom {M N P : SheafOfModules.{u} R}
    (f : M ⟶ N) (g : M ⟶ P)
    (e : ∀ U, (f.val.app U).hom.ker ≃ₗ[R.obj.obj U] P.val.obj U)
    (he : ∀ U c, e U c = g.val.app U c.1) :
    (sheafKernelIsoOfSectionEquiv R f g e he).hom = kernel.ι f ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

end
end PfaffianDescent
