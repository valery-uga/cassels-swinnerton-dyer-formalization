import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.IdealModulePullbackKernel

/-! A stalkwise criterion for monomorphisms of scheme modules. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- A morphism of scheme modules is monic if all of its additive-group
stalk maps are monic. -/
theorem schemeModule_mono_of_stalk_mono
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, Mono ((schemeModuleStalkFunctor X x).map φ)) :
    Mono φ := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hF : Mono (F.map φ) := by
    haveI : ∀ x : X, Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (F.map φ).hom) := by
      intro x
      change Mono ((schemeModuleStalkFunctor X x).map φ)
      exact h x
    exact TopCat.Presheaf.mono_of_stalk_mono (F.map φ)
  exact (Functor.reflectsMonomorphisms_of_faithful F).reflects φ hF

/-- Monicity of scheme-module morphisms can be checked on their
additive-group stalks. -/
theorem schemeModule_mono_iff_stalk_mono
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Mono φ ↔ ∀ x : X, Mono ((schemeModuleStalkFunctor X x).map φ) := by
  constructor
  · intro h x
    letI : Mono φ := h
    exact schemeModuleStalkFunctor_map_mono φ x
  · exact schemeModule_mono_of_stalk_mono φ

/-- The global closed-immersion ideal-kernel comparison is invertible
once the pullback of its ideal inclusion is monic on every stalk. -/
theorem isIso_closedImmersionIdealPullbackKernelComparison_of_stalk_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (h : ∀ x : X, Mono ((schemeModuleStalkFunctor X x).map
      ((Scheme.Modules.pullback f).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)))) :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  haveI : Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) :=
    schemeModule_mono_of_stalk_mono _ h
  exact isIso_closedImmersionIdealPullbackKernelComparison_of_mono f i

end PfaffianDescent
