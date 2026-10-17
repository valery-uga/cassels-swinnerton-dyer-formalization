import PfaffianDescent.VoisinSelectedOrderedGenericField

/-! The ordered generic residue point lifts through an integral affine open. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- The generic residue point of an integral scheme has a canonical lift
through an integral open immersion whose image contains the generic point. -/
noncomputable def openImmersion_genericResidueLift
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] :
    Spec (O.residueField (i (genericPoint U))) ⟶ U :=
  Spec.map (asIso (i.residueFieldMap (genericPoint U))).inv ≫
    U.fromSpecResidueField (genericPoint U)

/-- The lifted chart point is the actual generic residue point of the
ambient ordered scheme. -/
theorem openImmersion_genericResidueLift_comp
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] :
    openImmersion_genericResidueLift i ≫ i =
      O.fromSpecResidueField (i (genericPoint U)) := by
  let e := asIso (i.residueFieldMap (genericPoint U))
  calc
    openImmersion_genericResidueLift i ≫ i =
        Spec.map e.inv ≫
          (U.fromSpecResidueField (genericPoint U) ≫ i) := by
      rfl
    _ = Spec.map e.inv ≫
          (Spec.map e.hom ≫ O.fromSpecResidueField (i (genericPoint U))) := by
      simpa only [Category.assoc, e, asIso_hom] using
        congrArg (fun q : Spec (U.residueField (genericPoint U)) ⟶ O =>
          Spec.map e.inv ≫ q)
          (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
            i (genericPoint U)).symm
    _ = O.fromSpecResidueField (i (genericPoint U)) := by
      rw [← Category.assoc, ← Spec.map_comp, e.hom_inv_id, Spec.map_id,
        Category.id_comp]

/-- A coordinate lift on the selected open gives the same projective point
at the canonical generic residue field as the ambient coordinate map. -/
theorem openImmersion_genericResidueLift_coordinate_comp
    {U O W X : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (t : U ⟶ W) (j : W ⟶ X) (a : O ⟶ X)
    (ht : t ≫ j = i ≫ a) :
    (openImmersion_genericResidueLift i ≫ t) ≫ j =
      O.fromSpecResidueField (i (genericPoint U)) ≫ a := by
  rw [Category.assoc, ht, ← Category.assoc,
    openImmersion_genericResidueLift_comp]

end PfaffianDescent
