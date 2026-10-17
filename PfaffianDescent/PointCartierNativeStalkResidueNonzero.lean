import PfaffianDescent.FieldPointExtResiduePresentation

/-! # The actual residue presentation detects the actual nonzero local class -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe u

theorem pointCartierNativeStalkResidue_local_ne_zero
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [hExt : HasExt.{u} X.Modules]
    [hExtLocal : HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (e : Ext.{u} M N 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x M N e)
    (z : Ext.{u} M N 2) (hz : e z ≠ 0) :
    schemeModuleStalkModuleExtMap X (i x) M N 2 z ≠ 0 := by
  intro hzero
  apply hz
  rw [d.coordinate_eq]
  change (closedFieldPointResidueRingEquivAt i x)
    (localExtTwoResidueCoordinate d.f d.g d.hf d.hg d.hfm d.hgm
      ((Ext.mk₀ d.qM.inv).comp
        ((schemeModuleStalkModuleExtMap X (i x) M N 2 z).comp
          (Ext.mk₀ d.qN.hom) (add_zero 2)) (zero_add 2))) = 0
  simp only [hzero, Ext.zero_comp, Ext.comp_zero, map_zero]

end PfaffianDescent
