import PfaffianDescent.SectionRepresenterCechAugmentationComponents
import PfaffianDescent.SectionRepresenterCechCoefficientNaturality

/-!
# Refinement maps on section-representer Cech chains

A map of cover indices together with inclusions of cover members induces
the actual simplicial and chain maps. On Hom cochains this is restriction
to the refined intersections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {ι κ : Type u} (U : ι → C) (W : κ → C)
  (σ : κ → ι) (j : ∀ k, W k ⟶ U (σ k))

/-- The literal formal-coproduct morphism associated to a refinement. -/
def sectionRepresenterCoverRefinement : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι U where
  f := σ
  φ := j

/-- The simplicial refinement map, constructed by functoriality of the nerve. -/
def sectionRepresenterCechRefinementSimplicial :
    sectionRepresenterCechSimplicial R W ⟶ sectionRepresenterCechSimplicial R U :=
  Functor.whiskerRight (FormalCoproduct.cechFunctor.map
    (sectionRepresenterCoverRefinement U W σ j)) (sectionRepresenterFormalCoproductFunctor R)

/-- The actual chain map induced by a cover refinement. -/
def sectionRepresenterCechRefinement :
    sectionRepresenterCechChain R W ⟶ sectionRepresenterCechChain R U :=
  AlgebraicTopology.AlternatingFaceMapComplex.map
    (sectionRepresenterCechRefinementSimplicial R U W σ j)

set_option backward.isDefEq.respectTransparency false in
/-- On an ordered intersection, refinement is the product of the member
inclusions followed by the corresponding coarse-cover coproduct injection. -/
theorem sectionRepresenterCechRefinement_component (n : ℕ) (f : Fin (n + 1) → κ) :
    Sigma.ι (fun g : Fin (n + 1) → κ =>
        sectionRepresenter R (∏ᶜ fun a : Fin (n + 1) => W (g a))) f ≫
      (sectionRepresenterCechRefinement R U W σ j).f n =
    (sectionRepresenterFunctor R).map
      (CategoryTheory.Limits.Pi.map (fun a : Fin (n + 1) => j (f a))) ≫
      Sigma.ι (fun g : Fin (n + 1) → ι =>
        sectionRepresenter R (∏ᶜ fun a : Fin (n + 1) => U (g a))) (σ ∘ f) := by
  exact sectionRepresenterFormalCoproductFunctor_ι_map R _ _
    (FormalCoproduct.powerMap (sectionRepresenterCoverRefinement U W σ j)
      (Fin (n + 1))) f

set_option backward.isDefEq.respectTransparency false in
/-- Refinement respects the actual augmentation after normalizing its
formal singleton target to the common terminal-open representer. -/
theorem sectionRepresenterCechRefinement_augmentation (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechRefinement R U W σ j).f 0 ≫
      sectionRepresenterCechAugmentation R U T hT ≫
        (sectionRepresenterCechTargetIsoTerminal R U T hT).hom =
    sectionRepresenterCechAugmentation R W T hT ≫
      (sectionRepresenterCechTargetIsoTerminal R W T hT).hom := by
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun g : Fin 1 → κ =>
      sectionRepresenter R (∏ᶜ fun a : Fin 1 => W (g a))) f ≫
        (sectionRepresenterCechRefinement R U W σ j).f 0 ≫
          sectionRepresenterCechAugmentation R U T hT ≫
            (sectionRepresenterCechTargetIsoTerminal R U T hT).hom =
    Sigma.ι (fun g : Fin 1 → κ =>
      sectionRepresenter R (∏ᶜ fun a : Fin 1 => W (g a))) f ≫
        sectionRepresenterCechAugmentation R W T hT ≫
          (sectionRepresenterCechTargetIsoTerminal R W T hT).hom
  rw [← Category.assoc, sectionRepresenterCechRefinement_component,
    Category.assoc, sectionRepresenterCechAugmentation_component,
    sectionRepresenterCechAugmentation_component, ← Functor.map_comp]
  congr 1
  exact hT.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- In section coordinates, Hom pullback along refinement is literal
restriction to the smaller ordered intersection. -/
theorem sectionRepresenterCechHomEquivPi_refinement
    (M : SheafOfModules.{u} R) (n : ℕ)
    (h : (sectionRepresenterCechChain R U).X n ⟶ M) (f : Fin (n + 1) → κ) :
    sectionRepresenterCechHomEquivPi R W M n
        ((sectionRepresenterCechRefinement R U W σ j).f n ≫ h) f =
      M.val.map (CategoryTheory.Limits.Pi.map (fun a : Fin (n + 1) => j (f a))).op
        (sectionRepresenterCechHomEquivPi R U M n h (σ ∘ f)) := by
  change sectionRepresenterHomEquiv R (∏ᶜ fun a : Fin (n + 1) => W (f a)) M
    (Sigma.ι (fun g : Fin (n + 1) → κ =>
      sectionRepresenter R (∏ᶜ fun a : Fin (n + 1) => W (g a))) f ≫
        ((sectionRepresenterCechRefinement R U W σ j).f n ≫ h)) = _
  rw [← Category.assoc, sectionRepresenterCechRefinement_component, Category.assoc]
  exact sectionRepresenterHomEquiv_precomp R _ M _

end PfaffianDescent
