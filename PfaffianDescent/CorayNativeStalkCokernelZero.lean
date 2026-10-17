import PfaffianDescent.VoisinSheafStalk
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! SOURCE ONLY / UNCHECKED. Ordinary generic scheme cut for the actual
native module-stalk functor and its actual cokernel comparison. This keeps
typeclass construction before specialization to Proj's module category. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Bijectivity of the SAME actual native stalk map annihilates the actual
cokernel stalk. All functor additivity and preservation are derived here
with X abstract, rather than supplied at the actual geometric caller. -/
theorem nativeSchemeModule_cokernelStalk_subsingleton_of_bijective
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : X)
    (hbij : Function.Bijective (schemeModuleStalkLinearMap f x)) :
    Subsingleton ((Scheme.Modules.presheaf (X := X) (cokernel f)).stalk x) := by
  let F := schemeModuleStalkModuleFunctor X x
  letI : F.Additive := inferInstanceAs ((schemeModuleStalkModuleFunctor X x).Additive)
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : IsIso (F.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hzero : IsZero (F.obj (cokernel f)) :=
    (isZero_cokernel_of_epi (F.map f)).of_iso (PreservesCokernel.iso F f)
  exact ModuleCat.subsingleton_of_isZero hzero

end PfaffianDescent.Coray
