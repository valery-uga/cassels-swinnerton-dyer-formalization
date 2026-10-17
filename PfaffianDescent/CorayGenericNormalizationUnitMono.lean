import PfaffianDescent.CorayGenericNormalizationQuotientSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! Actual generic normalization unit is mono and its literal cokernel
sequence is short exact. No finite normalization, section injection, Mono,
short-exactness or genus certificate is supplied as a premise.
STATUS: UNVERIFIED SOURCE ONLY. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual generic-point section map is injective on every nonempty
open, because its actual function-field comparison is the injective germ. -/
theorem integralGenericPointMap_app_injective
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective ((X.fromSpecStalk (genericPoint X)).app U) := by
  intro a b hab
  apply X.germToFunctionField_injective U
  have h := congrArg (fun z => (integralGenericPointPreimageSectionsIso X U).hom z) hab
  change (((X.fromSpecStalk (genericPoint X)).app U ≫
      (integralGenericPointPreimageSectionsIso X U).hom).hom a) =
    (((X.fromSpecStalk (genericPoint X)).app U ≫
      (integralGenericPointPreimageSectionsIso X U).hom).hom b) at h
  rw [integralGenericPointPreimageSectionsIso_comp_app] at h
  exact h

/-- The actual normalization section map is injective on every open.
This follows from its actual generic-point factorization; the empty open
has a subsingleton section ring. No injected-section premise is used. -/
theorem genericNormalization_fromNormalization_app_injective
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    Function.Injective ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  by_cases hU : Nonempty U
  · letI : Nonempty U := hU
    letI : Mono (f.app U) := ConcreteCategory.mono_of_injective _
      (integralGenericPointMap_app_injective X U)
    have hcomp : Mono ((f.toNormalization ≫ f.fromNormalization).app U) := by
      rw [Scheme.Hom.congr_app f.toNormalization_fromNormalization U]
      infer_instance
    letI : Mono (f.fromNormalization.app U ≫
        f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
      simpa only [Scheme.Hom.comp_app] using hcomp
    apply (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    exact mono_of_mono (f.fromNormalization.app U)
      (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U))
  · have hbot : U = ⊥ := by
      ext x
      exact iff_false_intro (fun hx => hU ⟨⟨x, hx⟩⟩)
    haveI : Subsingleton Γ(X, U) := by
      rw [hbot]
      infer_instance
    intro a b hab
    exact Subsingleton.elim a b

/-- The canonical GLOBAL normalization unit is an actual monomorphism
of original scheme modules, proved internally from its actual components. -/
theorem genericNormalizationUnitToPushforwardUnit_mono
    (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    Mono (genericNormalizationUnitToPushforwardUnit X) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective ((genericNormalizationUnitToPushforwardUnit X).val.app U)
  intro a b hab
  apply genericNormalization_fromNormalization_app_injective X U.unop
  change ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U.unop a) =
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U.unop b) at hab
  exact hab

/-- The original structure sheaf, actual normalization pushforward and
ACTUAL quotient sheaf form an actual short-exact cokernel sequence.
The third object is definitionally genericNormalizationQuotientSheaf X. -/
theorem genericNormalization_cokernelSequence_shortExact
    (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    (ShortComplex.cokernelSequence
      (genericNormalizationUnitToPushforwardUnit X)).ShortExact := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : Mono (genericNormalizationUnitToPushforwardUnit X) :=
    genericNormalizationUnitToPushforwardUnit_mono X
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact (genericNormalizationUnitToPushforwardUnit X))
    (by
      change Mono (genericNormalizationUnitToPushforwardUnit X)
      infer_instance)
    (by infer_instance)

end PfaffianDescent.Coray
