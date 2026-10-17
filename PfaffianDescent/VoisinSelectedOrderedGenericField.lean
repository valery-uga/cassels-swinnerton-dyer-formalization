import PfaffianDescent.VoisinSelectedQuotientFunctionField

/-! The selected ordered affine chart and its image generic point have the same field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- The fraction field of an integral ordered affine chart is the residue
field at its image generic point in the ordered configuration scheme. -/
noncomputable def affineOpenImmersion_fractionEquivGenericImageResidueField
    {U O : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] :
    FractionRing Γ(U, ⊤) ≃+* O.residueField (i (genericPoint U)) := by
  letI : Nonempty (⊤ : U.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty U), trivial⟩⟩
  letI : IsFractionRing Γ(U, ⊤) U.functionField :=
    functionField_isFractionRing_of_isAffineOpen U ⊤ (isAffineOpen_top U)
  have hgen : i (genericPoint U) = genericPoint O :=
    genericPoint_eq_of_isOpenImmersion i
  haveI : IsSimpleRing (O.presheaf.stalk (i (genericPoint U))) := by
    rw [hgen]
    infer_instance
  let e₀ := (FractionRing.algEquiv Γ(U, ⊤) U.functionField).toRingEquiv
  let e₁ := (asIso (i.stalkMap (genericPoint U))).symm.commRingCatIsoToRingEquiv
  let e₂ := RingEquiv.ofBijective (O.residue (i (genericPoint U))).hom
    ⟨(O.residue (i (genericPoint U))).hom.injective,
      IsLocalRing.residue_surjective⟩
  exact (e₀.trans e₁).trans e₂

/-- The generic-field equivalence evaluates a regular affine-chart
section at the corresponding generic residue point. -/
theorem affineOpenImmersion_fractionEquivGenericImageResidueField_algebraMap
    {U O : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] (s : Γ(U, ⊤)) :
    (i.residueFieldMap (genericPoint U)).hom
      (affineOpenImmersion_fractionEquivGenericImageResidueField i
        (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) s)) =
      U.Γevaluation (genericPoint U) s := by
  letI : Nonempty (⊤ : U.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty U), trivial⟩⟩
  letI : IsFractionRing Γ(U, ⊤) U.functionField :=
    functionField_isFractionRing_of_isAffineOpen U ⊤ (isAffineOpen_top U)
  let e₀ := (FractionRing.algEquiv Γ(U, ⊤) U.functionField).toRingEquiv
  have he₀ : e₀ (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) s) =
      U.germToFunctionField ⊤ s := by
    change (FractionRing.algEquiv Γ(U, ⊤) U.functionField)
      (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) s) =
        algebraMap Γ(U, ⊤) U.functionField s
    exact AlgEquiv.commutes _ s
  let t' : O.presheaf.stalk (i (genericPoint U)) :=
    (asIso (i.stalkMap (genericPoint U))).inv
      (U.germToFunctionField ⊤ s)
  have ht : (i.stalkMap (genericPoint U)).hom t' =
      U.germToFunctionField ⊤ s :=
    (asIso (i.stalkMap (genericPoint U))).inv_hom_id_apply _
  have he : affineOpenImmersion_fractionEquivGenericImageResidueField i
      (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) s) =
      (O.residue (i (genericPoint U))).hom t' := by
    change (O.residue (i (genericPoint U))).hom
      ((asIso (i.stalkMap (genericPoint U))).inv
        (e₀ (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) s))) = _
    rw [he₀]
  have hres := congrArg
    (fun f : O.presheaf.stalk (i (genericPoint U)) ⟶
        U.residueField (genericPoint U) => f t')
    (Scheme.residue_residueFieldMap i (genericPoint U))
  change (i.residueFieldMap (genericPoint U)).hom
      ((O.residue (i (genericPoint U))).hom t') =
    (U.residue (genericPoint U)).hom
      ((i.stalkMap (genericPoint U)).hom t') at hres
  rw [ht] at hres
  rw [he]
  exact hres

end PfaffianDescent
