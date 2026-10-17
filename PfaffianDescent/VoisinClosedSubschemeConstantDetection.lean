import PfaffianDescent.SchemeAffineFunctions
import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.VoisinSerreTwistSectionInjection

/-!
# Nonempty closed subschemes detect constant global functions

When all global functions on a scheme over a field come from the field, their
restriction to a subscheme with a nontrivial ring of global functions is
injective. This supplies the abstract final step for vanishing of global
sections of the ideal sheaf of a nonempty conic on a cubic surface.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- Constancy of global functions passes through a surjective restriction
map to a subscheme. -/
theorem affineFunctionHom_surjective_of_restriction_surjective
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    (hp : Function.Surjective (affineFunctionHom p))
    (hi : Function.Surjective i.appTop.hom) :
    Function.Surjective (affineFunctionHom (i ≫ p)) := by
  intro z
  obtain ⟨x, rfl⟩ := hi z
  obtain ⟨a, rfl⟩ := hp x
  exact ⟨a, by simp only [affineFunctionHom_comp, RingHom.comp_apply]⟩

/-- If all global functions on `X` come from a field, restriction to a
subscheme with a nontrivial global-function ring is injective. -/
theorem scheme_appTop_injective_of_groundField_constants
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [Nontrivial Γ(Z, ⊤)]
    (hsurj : Function.Surjective (affineFunctionHom p)) :
    Function.Injective i.appTop.hom := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  have hab : affineFunctionHom (i ≫ p) a =
      affineFunctionHom (i ≫ p) b := by
    simpa only [affineFunctionHom_comp, RingHom.comp_apply] using hxy
  exact congrArg (affineFunctionHom p)
    ((affineFunctionHom (i ≫ p)).injective hab)

/-- Under the canonical equivalence between pushed-forward unit-module
sections and regular functions, the module map induced by `i` is the usual
pullback of global functions. -/
theorem closedImmersionUnitToPushforward_sectionsMap_top
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (s : (SheafOfModules.unit X.ringCatSheaf).sections) :
    pushforwardUnitSectionsEquiv i
      (SheafOfModules.sectionsMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) s) =
      i.appTop.hom
        (moduleSectionsEquivTop X
          (SheafOfModules.unit X.ringCatSheaf) s) := by
  let M := SheafOfModules.unit Z.ringCatSheaf
  let N := (Scheme.Modules.pushforward i).obj M
  let eX := moduleSectionsEquivTop X N
  let eZ := moduleSectionsEquivTop Z M
  have hpush (t : N.sections) :
      pushforwardUnitSectionsEquiv i t = eX t := by
    change eZ (eZ.symm (eX t)) = eX t
    exact eZ.apply_symm_apply (eX t)
  rw [hpush]
  change
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app (op ⊤)
        (s.val (op ⊤)) =
      i.appTop.hom (s.val (op ⊤))
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    i.toRingCatSheafHom (X := op ⊤) (s.val (op ⊤))

/-- The map from global structure-sheaf sections to the pushed-forward
structure sheaf is injective under the constant-function hypothesis. -/
theorem closedImmersionUnitToPushforward_sectionsMap_injective_of_constants
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (i : Z ⟶ X)
    [Nontrivial Γ(Z, ⊤)]
    (hsurj : Function.Surjective (affineFunctionHom p)) :
    Function.Injective (SheafOfModules.sectionsMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) := by
  intro s t hst
  apply (moduleSectionsEquivTop X
    (SheafOfModules.unit X.ringCatSheaf)).injective
  apply scheme_appTop_injective_of_groundField_constants p i hsurj
  calc
    i.appTop.hom (moduleSectionsEquivTop X
        (SheafOfModules.unit X.ringCatSheaf) s) =
      pushforwardUnitSectionsEquiv i
        (SheafOfModules.sectionsMap
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) s) :=
      (closedImmersionUnitToPushforward_sectionsMap_top i s).symm
    _ = pushforwardUnitSectionsEquiv i
        (SheafOfModules.sectionsMap
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) t) :=
      congrArg (pushforwardUnitSectionsEquiv i) hst
    _ = i.appTop.hom (moduleSectionsEquivTop X
        (SheafOfModules.unit X.ringCatSheaf) t) :=
      closedImmersionUnitToPushforward_sectionsMap_top i t

/-- The ideal module of such a closed subscheme has only its zero global
section. In the conic application, this is `H⁰(O_S(-C))=0` after identifying
the conic ideal with the inverse-conic line bundle. -/
theorem closedImmersionModule_sections_subsingleton_of_constants
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (i : Z ⟶ X) [IsClosedImmersion i]
    [Nontrivial Γ(Z, ⊤)]
    (hsurj : Function.Surjective (affineFunctionHom p)) :
    Subsingleton (IdealSheafDataModule.closedImmersionModule i).sections := by
  exact subsingleton_left_sections_of_shortExact_of_right_sections_injective
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence i)
    (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i)
    (closedImmersionUnitToPushforward_sectionsMap_injective_of_constants
      p i hsurj)

/-- The nontriviality condition above follows from an actual point of the
closed subscheme. -/
theorem closedImmersionModule_sections_subsingleton_of_nonempty_constants
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (i : Z ⟶ X) [IsClosedImmersion i]
    [Nonempty Z]
    (hsurj : Function.Surjective (affineFunctionHom p)) :
    Subsingleton (IdealSheafDataModule.closedImmersionModule i).sections := by
  letI : Nonempty (⊤ : Z.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Z), by trivial⟩⟩
  exact closedImmersionModule_sections_subsingleton_of_constants p i hsurj

end PfaffianDescent
