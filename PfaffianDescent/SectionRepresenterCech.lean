import PfaffianDescent.CechExtVanishingLowDegree
import PfaffianDescent.SheafModuleMayerVietoris
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy

/-!
# The section-representer Čech chain

The free module sheaf represented by an open turns the Čech nerve of a finite
open family into an augmented simplicial object of sheaves of modules.  Its
alternating face-map complex is the source-side chain used by the acyclic-cover
criterion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extend the section-representer functor from site objects to formal
coproducts. -/
noncomputable def sectionRepresenterFormalCoproductFunctor :
    FormalCoproduct.{u} C ⥤ SheafOfModules.{u} R :=
  (FormalCoproduct.eval C (SheafOfModules.{u} R)).obj
    (sectionRepresenterFunctor R)

/-- The simplicial object of section representers attached to a finite Čech
nerve. -/
noncomputable def sectionRepresenterCechSimplicial
    {ι : Type u} (U : ι → C) : SimplicialObject (SheafOfModules.{u} R) :=
  (FormalCoproduct.mk _ U).cech ⋙
    sectionRepresenterFormalCoproductFunctor R

/-- The augmented simplicial section-representer object of a Čech nerve. -/
noncomputable def sectionRepresenterCechAugmented
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    SimplicialObject.Augmented (SheafOfModules.{u} R) :=
  (SimplicialObject.Augmented.whiskering
      (FormalCoproduct.{u} C) (SheafOfModules.{u} R)).obj
    (sectionRepresenterFormalCoproductFunctor R) |>.obj
      ((FormalCoproduct.mk _ U).cech.augmentOfIsTerminal
        (FormalCoproduct.isTerminalIncl T hT))

lemma sectionRepresenterCechAugmented_left
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechAugmented R U T hT).left =
      sectionRepresenterCechSimplicial R U := rfl

/-- The alternating chain complex underlying the section-representer Čech
nerve. -/
noncomputable def sectionRepresenterCechChain
    {ι : Type u} (U : ι → C) :
    ChainComplex (SheafOfModules.{u} R) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    (sectionRepresenterCechSimplicial R U)

lemma sectionRepresenterCechChain_obj
    {ι : Type u} (U : ι → C) (n : ℕ) :
    (sectionRepresenterCechChain R U).X n =
      ∐ fun f : Fin (n + 1) → ι =>
        sectionRepresenter R (∏ᶜ fun i : Fin (n + 1) => U (f i)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a degree of the section-representer Čech chain are the
families of sections on the corresponding ordered intersections. -/
noncomputable def sectionRepresenterCechHomEquivPi
    {ι : Type u} (U : ι → C) (M : SheafOfModules.{u} R) (n : ℕ) :
    ((sectionRepresenterCechChain R U).X n ⟶ M) ≃
      (∀ f : Fin (n + 1) → ι,
        M.val.obj (op (∏ᶜ fun i : Fin (n + 1) => U (f i)))) := by
  let E := (FormalCoproduct.mk _ U).cech
  let A := fun f : (E.obj (op (SimplexCategory.mk n))).I =>
    (sectionRepresenterFunctor R).obj
      ((E.obj (op (SimplexCategory.mk n))).obj f)
  exact
    { toFun := fun h f =>
        sectionRepresenterHomEquiv R
          ((E.obj (op (SimplexCategory.mk n))).obj f) M
          (Sigma.ι A f ≫ h)
      invFun := fun s =>
        Sigma.desc fun f =>
          (sectionRepresenterHomEquiv R
            ((E.obj (op (SimplexCategory.mk n))).obj f) M).symm (s f)
      left_inv := fun h => by
        apply Sigma.hom_ext
        intro f
        dsimp
        rw [Sigma.ι_desc, Equiv.symm_apply_apply]
      right_inv := fun s => by
        funext f
        dsimp
        rw [Sigma.ι_desc, Equiv.apply_symm_apply] }

end PfaffianDescent
