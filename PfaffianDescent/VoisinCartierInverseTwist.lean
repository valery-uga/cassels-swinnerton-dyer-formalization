import PfaffianDescent.ClosedImmersionIdealModuleCartierChart
import PfaffianDescent.VoisinSerreTwistSectionInjection
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# The inverse twist of a regular effective Cartier divisor

Mathlib currently has no scheme-level effective Cartier divisor object.
`RegularPrincipalImmersion` is the local regular-equation certificate used in
this project. Its inverse divisor twist is the actual ideal sheaf module of
the immersion. The chart trivializations below prove that this module is a
line bundle, and identify its inclusion into the structure sheaf with
multiplication by the chart equation. The same construction applies to a
conic divisor on a cubic surface once its regular-principal presentation is
available.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace RegularPrincipalImmersion

variable {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]

/-- The inverse twist `𝒪_X(-Z)` of a regular effective Cartier immersion is
its literal ideal subsheaf of `𝒪_X`. -/
noncomputable def inverseCartierTwist (H : RegularPrincipalImmersion i) :
    X.Modules :=
  IdealSheafDataModule.closedImmersionModule i

/-- The canonical inclusion `𝒪_X(-Z) ↪ 𝒪_X`. -/
noncomputable def inverseCartierTwistToUnit (H : RegularPrincipalImmersion i) :
    H.inverseCartierTwist ⟶ SheafOfModules.unit X.ringCatSheaf :=
  IdealSheafDataModule.closedImmersionModuleToUnit i

instance inverseCartierTwistToUnit_mono (H : RegularPrincipalImmersion i) :
    Mono H.inverseCartierTwistToUnit := by
  change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
  infer_instance

/-- This inverse twist is canonically the image-defined ideal module of the
actual closed immersion, with no abstract line-bundle replacement. -/
noncomputable def inverseCartierTwistIsoIdeal (H : RegularPrincipalImmersion i) :
    H.inverseCartierTwist ≅ IdealSheafDataModule.closedImmersionModule i :=
  Iso.refl _

theorem inverseCartierTwistIsoIdeal_hom_toUnit
    (H : RegularPrincipalImmersion i) :
    H.inverseCartierTwistIsoIdeal.hom ≫
        IdealSheafDataModule.closedImmersionModuleToUnit i =
      H.inverseCartierTwistToUnit := by
  change (𝟙 (IdealSheafDataModule.closedImmersionModule i)) ≫
      IdealSheafDataModule.closedImmersionModuleToUnit i =
    IdealSheafDataModule.closedImmersionModuleToUnit i
  simp only [Category.id_comp]

/-- An inverse Cartier twist is a line bundle: its regular-principal charts
trivialize it by a single generator. -/
theorem inverseCartierTwist_isLocallyFree
    (H : RegularPrincipalImmersion i) :
    H.inverseCartierTwist.IsLocallyFree :=
  H.closedImmersionModule_isLocallyFree

/-- The inverse Cartier twist participates in the literal ideal sequence
`0 → 𝒪_X(-Z) → 𝒪_X → i_*𝒪_Z → 0`. -/
theorem inverseCartierTwist_pushforwardSequence_shortExact
    (H : RegularPrincipalImmersion i) :
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).ShortExact :=
  IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i

/-- If the divisor detects global functions, its inverse twist has no
nonzero global section. -/
theorem inverseCartierTwist_sections_subsingleton_of_restriction_injective
    (H : RegularPrincipalImmersion i)
    (hinj : Function.Injective (SheafOfModules.sectionsMap
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).g)) :
    Subsingleton H.inverseCartierTwist.sections := by
  exact subsingleton_left_sections_of_shortExact_of_right_sections_injective
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence i)
    H.inverseCartierTwist_pushforwardSequence_shortExact hinj

end RegularPrincipalImmersion

end PfaffianDescent
