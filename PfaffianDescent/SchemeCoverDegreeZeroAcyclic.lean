import PfaffianDescent.ExtOneCoproductVanishing
import PfaffianDescent.SchemeCoverBoundaryCriterion

/-! # Degree-zero Cech terms of arbitrary acyclic covers -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u

/-- The selected categorical singleton product is the selected open itself. -/
theorem schemeOpen_singleton_product_eq {X : Scheme.{u}} {ι : Type u}
    (W : ι → X.Opens) (a : Fin 1 → ι) : (∏ᶜ fun k : Fin 1 => W (a k)) = W (a 0) := by
  apply le_antisymm
  · exact (Pi.π (fun k : Fin 1 => W (a k)) 0).le
  · exact (Pi.lift (fun k : Fin 1 => homOfLE (by
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      exact le_rfl))).le

set_option backward.isDefEq.respectTransparency false in
/-- Local degree-one acyclicity gives degree-one acyclicity of the actual
zero term even when the cover has infinitely many members. -/
theorem schemeCover_degree_zero_ext_one_subsingleton
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens)
    [hExt : HasExt.{u} X.Modules] (Y : X.Modules)
    [∀ i, Subsingleton (Ext.{u} (C := X.Modules)
      (sectionRepresenter X.ringCatSheaf (W i)) Y 1)] :
    Subsingleton (Ext.{u} (C := X.Modules)
      ((sectionRepresenterCechChain X.ringCatSheaf W).X 0) Y 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  let P : (Fin 1 → ι) → X.Modules := fun a =>
    sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 1 => W (a k))
  have hlocal (a : Fin 1 → ι) : Subsingleton (Ext.{u} (C := X.Modules) (P a) Y 1) := by
    have e := schemeOpen_singleton_product_eq W a
    dsimp only [P]
    rw [e]
    infer_instance
  letI : ∀ a, Subsingleton (Ext.{u} (C := X.Modules) (P a) Y 1) := hlocal
  exact ext_one_coproduct_subsingleton P Y
end PfaffianDescent
