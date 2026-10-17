import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! SOURCE ONLY / UNVERIFIED. Native ringed-site cut for the SAME original
subpresheaf inclusion, sheafification functor and adjunction counit. No
supplied Mono premise, scheme-site rewrite or replacement geometry. -/
noncomputable section
namespace PfaffianDescent.Coray
open CategoryTheory CategoryTheory.Limits
universe u v w
section NativeSite
variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Ordinary native-site equality exposes the SAME adjunction counit
factorization before any Scheme/TopCat presentation is substituted. -/
theorem nativeAssociatedSubpresheafToSheaf_eq_map_counit
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) (S : N.val.Submodule) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
        S.toPresheafOfModules N).symm S.ι =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map S.ι ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_counit
    S.toPresheafOfModules N S.ι

/-- The SAME original subpresheaf inclusion is monic by its subtype-valued
components; this is the native Submodule instance, not a hypothesis. -/
theorem nativeAssociatedSubpresheafInclusion_mono
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) (S : N.val.Submodule) :
    Mono S.ι := by
  infer_instance

/-- Native module sheafification preserves finite limits. -/
theorem nativeAssociatedSheafification_preservesFiniteLimits
    (R : Sheaf J RingCat.{u}) :
    PreservesFiniteLimits (PresheafOfModules.sheafification.{u} (𝟙 R.obj)) := by
  infer_instance

/-- The imported finite-limit preservation construction supplies the actual
functor's monomorphism-preservation instance. -/
theorem nativeAssociatedSheafification_preservesMonomorphisms
    (R : Sheaf J RingCat.{u}) :
    (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).PreservesMonomorphisms := by
  letI : PreservesFiniteLimits
      (PresheafOfModules.sheafification.{u} (𝟙 R.obj)) :=
    nativeAssociatedSheafification_preservesFiniteLimits R
  exact preservesMonomorphisms_of_preservesLimitsOfShape
    (PresheafOfModules.sheafification.{u} (𝟙 R.obj))

/-- The SAME functor sends the SAME original subpresheaf inclusion to a Mono. -/
theorem nativeAssociatedSubpresheafSheafificationMap_mono
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) (S : N.val.Submodule) :
    Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map S.ι) := by
  letI : Mono S.ι := nativeAssociatedSubpresheafInclusion_mono R N S
  letI : (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).PreservesMonomorphisms :=
    nativeAssociatedSheafification_preservesMonomorphisms R
  exact Functor.PreservesMonomorphisms.preserves S.ι

/-- The original native sheafification counit is an Iso as a natural
transformation, hence its actual component at N is an Iso. -/
theorem nativeAssociatedSheafificationCounitApp_isIso
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) :
    IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N) := by
  letI : IsIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit :=
    inferInstance
  exact NatIso.isIso_app_of_isIso
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit N

/-- In particular, the original counit component is monic. -/
theorem nativeAssociatedSheafificationCounitApp_mono
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) :
    Mono ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N) := by
  letI : IsIso
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N) :=
    nativeAssociatedSheafificationCounitApp_isIso R N
  infer_instance

/-- Compose the explicitly constructed two native Monos, retaining the
SAME original inclusion, functor and counit. No Mono premise is supplied. -/
theorem nativeAssociatedSubpresheafMapCounit_mono
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) (S : N.val.Submodule) :
    Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map S.ι ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N) := by
  letI : Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map S.ι) :=
    nativeAssociatedSubpresheafSheafificationMap_mono R N S
  letI : Mono
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app N) :=
    nativeAssociatedSheafificationCounitApp_mono R N
  exact mono_comp' (nativeAssociatedSubpresheafSheafificationMap_mono R N S)
    (nativeAssociatedSheafificationCounitApp_mono R N)

/-- The original transposed subpresheaf inclusion is monic. The rewrite
is performed ONLY with the abstract native site and actual ring sheaf. -/
theorem nativeAssociatedSubpresheafToSheaf_mono
    (R : Sheaf J RingCat.{u}) (N : SheafOfModules.{u} R) (S : N.val.Submodule) :
    Mono (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv
      S.toPresheafOfModules N).symm S.ι) := by
  rw [nativeAssociatedSubpresheafToSheaf_eq_map_counit]
  exact nativeAssociatedSubpresheafMapCounit_mono R N S

end NativeSite
end PfaffianDescent.Coray
