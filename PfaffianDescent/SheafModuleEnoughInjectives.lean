import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Enough injectives for sheaves of modules

The Serre construction uses an `Ext¹` class in the abelian category of
module sheaves.  This file supplies the categorical input needed to realize
such a class by a short exact sequence: module presheaves form a
Grothendieck abelian category, and exact sheafification transfers that
structure to module sheaves.

The result is kept as a theorem rather than a global instance.  This keeps
typeclass search for unrelated sheaf categories small while making the
construction available exactly where the Serre argument needs it.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})

/-- Filtered colimits of module presheaves are exact.  The forgetful functor
to additive presheaves reflects the relevant exactness statement. -/
theorem presheafModulesAB5 :
    AB5OfSize.{u, u} (PresheafOfModules.{u} R.obj) where
  ofShape I _ _ := by
    let _ : AB5OfSize.{u, u} (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
      { ofShape := fun I _ _ => by
          let _ : HasExactColimitsOfShape I AddCommGrpCat.{u} := AB5OfSize.ofShape I
          infer_instance }
    exact HasExactColimitsOfShape.domain_of_functor I
      (PresheafOfModules.toPresheaf R.obj)

/-- The coproduct of free modules on representables is a separator for
module presheaves. -/
theorem presheafModulesHasSeparator :
    HasSeparator (PresheafOfModules.{u} R.obj) where
  hasSeparator := by
    refine ⟨∐ (fun X : C => (yoneda ⋙ PresheafOfModules.free R.obj).obj X), ?_⟩
    exact (PresheafOfModules.freeYoneda.isSeparating R.obj).isSeparator_coproduct

/-- Module presheaves form a Grothendieck abelian category. -/
theorem presheafModulesGrothendieck :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R.obj) where
  ab5OfSize := presheafModulesAB5 R
  hasSeparator := presheafModulesHasSeparator R

/-- A left adjoint carries a separator to a separator when its right adjoint
is fully faithful.  Applied below, the left adjoint is sheafification and the
right adjoint is the inclusion of sheaves into presheaves. -/
lemma isSeparator_map_of_adjunction
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {Q : B ⥤ A} (adj : L ⊣ Q) [Q.Full] [Q.Faithful]
    {G : A} (hG : IsSeparator G) : IsSeparator (L.obj G) := by
  rw [isSeparator_def]
  intro X Y f g h
  apply Q.map_injective
  apply hG.def
  intro k
  let t : L.obj G ⟶ X := (adj.homEquiv G X).symm k
  have ht := h t
  have ht' := congrArg (adj.homEquiv G Y) ht
  simpa only [t, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] using ht'

variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Exact sheafification sends a presheaf separator to a separator of module
sheaves. -/
theorem sheafModulesHasSeparator :
    HasSeparator (SheafOfModules.{u} R) where
  hasSeparator := by
    obtain ⟨G, hG⟩ := (presheafModulesHasSeparator R).hasSeparator
    let L := PresheafOfModules.sheafification (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
    exact ⟨L.obj G, isSeparator_map_of_adjunction adj hG⟩

/-- Exact sheafification preserves exact filtered colimits of module
presheaves. -/
theorem sheafModulesAB5 : AB5OfSize.{u, u} (SheafOfModules.{u} R) where
  ofShape I _ _ := by
    let _ : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R.obj) :=
      presheafModulesGrothendieck R
    exact Adjunction.hasExactColimitsOfShape
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) I

/-- Module sheaves form a Grothendieck abelian category. -/
theorem sheafModulesGrothendieck :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where
  ab5OfSize := sheafModulesAB5 R
  hasSeparator := sheafModulesHasSeparator R

/-- The category of sheaves of modules over a sheaf of rings has enough
injectives.  This is the categorical realization input for the `Ext¹` class
in Voisin's Serre construction. -/
theorem sheafOfModules_enoughInjectives :
    EnoughInjectives (SheafOfModules.{u} R) := by
  let _ : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
    sheafModulesGrothendieck R
  infer_instance

end PfaffianDescent
