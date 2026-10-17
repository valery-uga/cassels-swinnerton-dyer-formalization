import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
import Mathlib.Algebra.Module.Projective

namespace PfaffianDescent
open ModuleCat CategoryTheory CategoryTheory.Limits
universe u
section
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

instance coextension_additive : (coextendScalars f).Additive where
  map_add {X Y} g h := by
    ext x s
    rfl

/-- Coextension takes injective modules to injective modules. -/
theorem coextension_injective (M : ModuleCat.{u} R) (hM : CategoryTheory.Injective M) :
    CategoryTheory.Injective ((coextendScalars f).obj M) :=
  (restrictCoextendScalarsAdj f).map_injective M hM

/-- Coextension preserves surjections when the algebra is projective over the base. -/
theorem coextension_surjective
    [Module.Projective R ((restrictScalars f).obj (ModuleCat.of A A))]
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (hg : Function.Surjective g) :
    Function.Surjective ((coextendScalars f).map g) := by
  intro psi
  obtain ⟨h, hh⟩ := Module.projective_lifting_property g.hom
    (CoextendScalars.equiv f N psi) hg
  refine ⟨(CoextendScalars.equiv f M).symm h, CoextendScalars.ext ?_⟩
  ext x
  exact LinearMap.congr_fun hh x

/-- Applying coextension to a short exact sequence remains short exact over a
projective algebra. -/
theorem coextension_shortExact
    [Module.Projective R ((restrictScalars f).obj (ModuleCat.of A A))]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (coextendScalars f)).ShortExact where
  exact := hS.exact.map_of_mono_of_preservesKernel (coextendScalars f)
    hS.mono_f inferInstance
  mono_f := by
    let := hS.mono_f
    change Mono ((coextendScalars f).map S.f)
    infer_instance
  epi_g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact coextension_surjective f S.g ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)

end
end PfaffianDescent
