import AllCharacteristics.GenericPointDominance
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericField

/-! Every actual generic field point factors through the literal generic
residue point. This supplies the ordered component coefficient map. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_genericFieldPoint_exists_residueFactor
    {O : Scheme.{u}} [IsIntegral O] {L : Type u} [Field L]
    (c : Spec (.of L) ⟶ O)
    (hc : c (IsLocalRing.closedPoint L) = genericPoint O) :
    ∃ g : O.residueField (genericPoint O) →+* L,
      Spec.map (CommRingCat.ofHom g) ≫
        O.fromSpecResidueField (genericPoint O) = c := by
  let e : O.functionField ≃+* O.residueField (genericPoint O) :=
    RingEquiv.ofBijective (O.residue (genericPoint O)).hom
      ⟨(O.residue (genericPoint O)).hom.injective,
        IsLocalRing.residue_surjective⟩
  let f := O.genericFieldPointRingHom c hc
  let g := f.comp e.symm.toRingHom
  refine ⟨g, ?_⟩
  have hcomp : O.residue (genericPoint O) ≫ CommRingCat.ofHom g =
      CommRingCat.ofHom f := by
    ext r
    exact congrArg f (e.symm_apply_apply r)
  change Spec.map (CommRingCat.ofHom g) ≫
    (Spec.map (O.residue (genericPoint O)) ≫ O.fromSpecStalk (genericPoint O)) = c
  rw [← Category.assoc, ← Spec.map_comp, hcomp]
  exact O.genericFieldPointRingHom_spec c hc

end PfaffianDescent
