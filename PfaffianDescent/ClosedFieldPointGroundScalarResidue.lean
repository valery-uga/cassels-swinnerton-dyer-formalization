import PfaffianDescent.FieldPointExtCoordinate
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! # Ground-field constants in the actual closed-point residue coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

/-- A point compatible with the given field extension pulls back ground-field
constants to the actual corresponding constants on its field spectrum. -/
theorem fieldPoint_appTop_ground_constant
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L))) (c : K) :
    i.appTop (affineFunctionHom base c) =
      affineFunctionHom (𝟙 (Spec (.of L))) (algebraMap K L c) := by
  have h := RingHom.congr_fun (affineFunctionHom_comp i base) c
  rw [hi] at h
  have hs := affineFunctionHom_comp_Spec (𝟙 (Spec (.of L))) (algebraMap K L)
  rw [Category.id_comp] at hs
  exact h.symm.trans (RingHom.congr_fun hs c)

set_option backward.isDefEq.respectTransparency false in
/-- The actual closed-point residue coordinate sends the germ of a base constant
to its image under the specified field extension. -/
theorem closedFieldPointResidueRingEquivAt_ground_constant_germ_top
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (x : Spec (.of L)) (c : K) :
    closedFieldPointResidueRingEquivAt i x
      (X.residue (i x) (X.presheaf.germ ⊤ (i x) trivial
        (affineFunctionHom base c))) = algebraMap K L c := by
  rw [closedFieldPointResidueRingEquivAt_residue_eq_stalkMap,
    Scheme.Hom.germ_stalkMap_apply]
  change specFieldStalkRingEquivAt x
    ((Spec (.of L)).presheaf.germ ⊤ x trivial
      (i.appTop (affineFunctionHom base c))) = _
  rw [fieldPoint_appTop_ground_constant base i hi c]
  exact specFieldStalkRingEquivAt_germ_affineFunctionHom_id x _

set_option backward.isDefEq.respectTransparency false in
/-- The same ground-field residue formula on any actual neighborhood of the point. -/
theorem closedFieldPointResidueRingEquivAt_ground_constant_germ
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (x : Spec (.of L)) (U : X.Opens) (hx : i x ∈ U) (c : K) :
    closedFieldPointResidueRingEquivAt i x
      (X.residue (i x) (X.presheaf.germ U (i x) hx
        (schemeOpenBaseRingHom base U c))) = algebraMap K L c := by
  change closedFieldPointResidueRingEquivAt i x
    (X.residue (i x) (X.presheaf.germ U (i x) hx
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (affineFunctionHom base c)))) = _
  rw [TopCat.Presheaf.germ_res_apply]
  exact closedFieldPointResidueRingEquivAt_ground_constant_germ_top base i hi x c

end PfaffianDescent
