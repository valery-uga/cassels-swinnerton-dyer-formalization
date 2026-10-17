import PfaffianDescent.ActualLocalizedBasisComparison
import Mathlib.Algebra.Category.ModuleCat.Basic

/- SOURCE ONLY / UNVERIFIED. A bundled-functor comparison. The actual
basis caller derives target denominator units from the real tilde sheaf
and inclusion of basic opens; no such certificate survives that caller. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u

/-- Localization comparison is natural for actual bundled module functors.
The target denominator condition is an auxiliary algebra input, internally
derived from the coefficient ring in the actual Spec R application. -/
def actualLocalizedFunctorComparison
    {R : Type u} [CommRing R] {C : Type u} [Category C]
    (M : ModuleCat R) (F G : C ⥤ ModuleCat R)
    (f : (Functor.const C).obj M ⟶ F)
    (g : (Functor.const C).obj M ⟶ G)
    (S : C → Submonoid R)
    (hf : ∀ c, IsLocalizedModule (S c) (f.app c).hom)
    (hg : ∀ c, IsLocalizedModule (S c) (g.app c).hom)
    (hunit : ∀ (c d : C) (i : c ⟶ d) (s : S c),
      IsUnit (algebraMap R (Module.End R (G.obj d)) s)) : F ≅ G := by
  letI hFLoc (c : C) : IsLocalizedModule (S c) (f.app c).hom := hf c
  letI hGLoc (c : C) : IsLocalizedModule (S c) (g.app c).hom := hg c
  refine NatIso.ofComponents (fun c =>
    (IsLocalizedModule.linearEquiv (S c) (f.app c).hom (g.app c).hom).toModuleIso) ?_
  intro c d i
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (S c) (f.app c).hom (hunit c d i)
  apply LinearMap.ext
  intro m
  have hF : f.app c ≫ F.map i = f.app d :=
    (f.naturality i).symm.trans (Category.id_comp (f.app d))
  have hG : g.app c ≫ G.map i = g.app d :=
    (g.naturality i).symm.trans (Category.id_comp (g.app d))
  change IsLocalizedModule.linearEquiv (S d) (f.app d).hom (g.app d).hom
      (F.map i (f.app c m)) =
    G.map i (IsLocalizedModule.linearEquiv (S c) (f.app c).hom (g.app c).hom
      (f.app c m))
  exact (congrArg
      (fun x => IsLocalizedModule.linearEquiv (S d) (f.app d).hom (g.app d).hom x)
      (ConcreteCategory.congr_hom hF m)).trans
    ((IsLocalizedModule.linearEquiv_apply (S d) (f.app d).hom (g.app d).hom m).trans
      ((ConcreteCategory.congr_hom hG m).symm.trans
        (congrArg (fun x => G.map i x)
          (IsLocalizedModule.linearEquiv_apply (S c) (f.app c).hom (g.app c).hom m).symm)))

/-- Exact action on the shared original module. -/
lemma actualLocalizedFunctorComparison_on_source
    {R : Type u} [CommRing R] {C : Type u} [Category C]
    (M : ModuleCat R) (F G : C ⥤ ModuleCat R)
    (f : (Functor.const C).obj M ⟶ F)
    (g : (Functor.const C).obj M ⟶ G)
    (S : C → Submonoid R)
    (hf : ∀ c, IsLocalizedModule (S c) (f.app c).hom)
    (hg : ∀ c, IsLocalizedModule (S c) (g.app c).hom)
    (hunit : ∀ (c d : C) (i : c ⟶ d) (s : S c),
      IsUnit (algebraMap R (Module.End R (G.obj d)) s))
    (c : C) (m : M) :
    (actualLocalizedFunctorComparison M F G f g S hf hg hunit).hom.app c
      (f.app c m) = g.app c m := by
  letI : IsLocalizedModule (S c) (f.app c).hom := hf c
  letI : IsLocalizedModule (S c) (g.app c).hom := hg c
  exact IsLocalizedModule.linearEquiv_apply (S c) (f.app c).hom (g.app c).hom m

end PfaffianDescent
