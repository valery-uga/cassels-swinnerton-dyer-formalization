import PfaffianDescent.SectionRepresenterCechRefinement
import PfaffianDescent.SectionRepresenterCechVertexMap

/-! # Actual refinement of vertex maps -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Refinement of a degree-zero vertex map is the map of the actual
refined vertex morphisms. -/
theorem sectionRepresenterCechVertexMap_refinement
    {ι κ : Type u} (U : ι → C) (W : κ → C) (σ : κ → ι)
    (j : ∀ k, W k ⟶ U (σ k)) (M : SheafOfModules.{u} R)
    (v : ∀ i, sectionRepresenter R (U i) ⟶ M) :
    (sectionRepresenterCechRefinement R U W σ j).f 0 ≫
        sectionRepresenterCechVertexMap R U M v =
      sectionRepresenterCechVertexMap R W M
        (fun k => (sectionRepresenterFunctor R).map (j k) ≫ v (σ k)) := by
  apply Sigma.hom_ext
  intro s
  change (Fin 1 → κ) at s
  change Sigma.ι (fun g : Fin 1 → κ => sectionRepresenter R (∏ᶜ fun k : Fin 1 => W (g k))) s ≫
      ((sectionRepresenterCechRefinement R U W σ j).f 0 ≫
        sectionRepresenterCechVertexMap R U M v) =
    Sigma.ι (fun g : Fin 1 → κ => sectionRepresenter R (∏ᶜ fun k : Fin 1 => W (g k))) s ≫
      sectionRepresenterCechVertexMap R W M
        (fun k => (sectionRepresenterFunctor R).map (j k) ≫ v (σ k))
  rw [← Category.assoc, sectionRepresenterCechRefinement_component,
    Category.assoc, sectionRepresenterCechVertexMap_component,
    sectionRepresenterCechVertexMap_component]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun k => (sectionRepresenterFunctor R).map k ≫ v (σ (s 0)))
    (Pi.map_π (fun a : Fin 1 => j (s a)) (0 : Fin 1))
end PfaffianDescent
