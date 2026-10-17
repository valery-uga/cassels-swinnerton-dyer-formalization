import PfaffianDescent.SectionRepresenterCechVertexMap

/-!
# Components of the actual Cech augmentation

The formal singleton target of the augmentation is identified with the
terminal-open representer. Its component on an overlap is the map induced
by the unique morphism into that terminal open.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Identify the formal singleton augmentation target with its representer. -/
def sectionRepresenterCechTargetIsoTerminal
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    (sectionRepresenterCechAugmented R U T hT).right ≅ sectionRepresenter R T :=
  ((FormalCoproduct.evalCompInclIsoId _ _).app (sectionRepresenterFunctor R)).app T

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterCechAugmentation_component
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) (f : Fin 1 → ι) :
    Sigma.ι (fun g : Fin 1 → ι =>
        sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (g k))) f ≫
      sectionRepresenterCechAugmentation R U T hT ≫
        (sectionRepresenterCechTargetIsoTerminal R U T hT).hom =
      (sectionRepresenterFunctor R).map (hT.from (∏ᶜ fun k : Fin 1 => U (f k))) := by
  let E := (FormalCoproduct.mk _ U).cech
  let d := (FormalCoproduct.isTerminalIncl T hT).from (E.obj (op ⦋0⦌))
  change Sigma.ι (fun g : (E.obj (op ⦋0⦌)).I =>
      (sectionRepresenterFunctor R).obj ((E.obj (op ⦋0⦌)).obj g)) f ≫
      (sectionRepresenterFormalCoproductFunctor R).map d ≫
        (sectionRepresenterCechTargetIsoTerminal R U T hT).hom = _
  rw [← Category.assoc, sectionRepresenterFormalCoproductFunctor_ι_map,
    Category.assoc]
  change (sectionRepresenterFunctor R).map (d.φ f) ≫
    (Sigma.ι (fun _ : PUnit => (sectionRepresenterFunctor R).obj T) (d.f f) ≫
      Sigma.desc (fun _ : PUnit => 𝟙 ((sectionRepresenterFunctor R).obj T))) = _
  rw [Sigma.ι_desc]
  change ((sectionRepresenterFunctor R).map
      (hT.from (∏ᶜ fun k : Fin 1 => U (f k))) :
      sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (f k)) ⟶ sectionRepresenter R T) ≫
    𝟙 (sectionRepresenter R T) = _
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The normalized augmentation is the degree-zero vertex map induced
by the terminal-open inclusions. -/
theorem sectionRepresenterCechAugmentation_eq_vertexMap
    {ι : Type u} (U : ι → C) (T : C) (hT : IsTerminal T) :
    sectionRepresenterCechAugmentation R U T hT ≫
        (sectionRepresenterCechTargetIsoTerminal R U T hT).hom =
      sectionRepresenterCechVertexMap R U (sectionRepresenter R T)
        (fun i => (sectionRepresenterFunctor R).map (hT.from (U i))) := by
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun g : Fin 1 → ι =>
      sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (g k))) f ≫
      sectionRepresenterCechAugmentation R U T hT ≫
        (sectionRepresenterCechTargetIsoTerminal R U T hT).hom =
    Sigma.ι (fun g : Fin 1 → ι =>
      sectionRepresenter R (∏ᶜ fun k : Fin 1 => U (g k))) f ≫
      sectionRepresenterCechVertexMap R U (sectionRepresenter R T)
        (fun i => (sectionRepresenterFunctor R).map (hT.from (U i)))
  rw [sectionRepresenterCechAugmentation_component,
    sectionRepresenterCechVertexMap_component, ← Functor.map_comp]
  congr 1
  exact hT.hom_ext _ _

end PfaffianDescent
