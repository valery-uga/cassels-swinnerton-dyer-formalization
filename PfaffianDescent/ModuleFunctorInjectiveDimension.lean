import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits ModuleCat
universe u
section
variable {R S : Type u} [CommRing R] [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects]

/-- An exact functor preserving injectives does not increase injective dimension. -/
theorem moduleFunctor_hasInjectiveDimensionLE (n : ℕ) (M : ModuleCat.{u} R)
    [HasInjectiveDimensionLE M n] : HasInjectiveDimensionLE (F.obj M) n := by
  induction n generalizing M with
  | zero =>
    letI : CategoryTheory.Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr inferInstance
    infer_instance
  | succ n ih =>
    obtain ⟨I, _, i, _⟩ := EnoughInjectives.presentation M
    let T : ShortComplex (ModuleCat R) := ModuleCat.shortComplexOfCompEqZero
      i.hom i.hom.range.mkQ i.hom.exact_map_mkQ_range.linearMap_comp_eq_zero
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      i.hom.exact_map_mkQ_range ((mono_iff_injective i).mp inferInstance)
      (Submodule.mkQ_surjective _)
    letI : HasInjectiveDimensionLE T.X₃ n :=
      (hT.hasInjectiveDimensionLT_X₃_iff n inferInstance).mpr inferInstance
    have h3 : HasInjectiveDimensionLT (T.map F).X₃ (n+1) := ih T.X₃
    have h2 : HasInjectiveDimensionLT (T.map F).X₂ (n+1+1) := by
      change HasInjectiveDimensionLT (F.obj I) (n+1+1)
      infer_instance
    exact (hT.map_of_exact F).hasInjectiveDimensionLT_X₁ (n+1) h3 h2

end
end PfaffianDescent
