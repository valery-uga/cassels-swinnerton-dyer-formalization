import Mathlib.AlgebraicGeometry.Pullbacks
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u

theorem cubicConfigurationGenericMarkedOutsideSupport_not_mem_pullback_support
    {X Y D : Scheme.{u}} (q : Y ⟶ X) (i : D ⟶ X) (x : Y)
    (hx : q x ∉ Set.range i) : x ∉ Set.range (pullback.fst q i) := by
  rintro ⟨z, hz⟩
  apply hx
  refine ⟨pullback.snd q i z, ?_⟩
  have he := congrArg (fun f => f z) (pullback.condition (f := q) (g := i))
  simp only [Scheme.Hom.comp_apply] at he
  exact he.symm.trans (congrArg q hz)

theorem cubicConfigurationGenericMarkedOutsideSupport_not_mem_pullback_source_support
    {X Y D T : Scheme.{u}} (q : Y ⟶ X) (i : D ⟶ X)
    (v : T ⟶ pullback q i) (x : Y) (hx : q x ∉ Set.range i) :
    x ∉ Set.range (v ≫ pullback.fst q i) := by
  intro h
  apply cubicConfigurationGenericMarkedOutsideSupport_not_mem_pullback_support q i x hx
  rcases h with ⟨z, hz⟩
  exact ⟨v z, hz⟩
end PfaffianDescent
