import PfaffianDescent.ClosedImmersionPointLift

/-!
# Residue fields at closed field-valued points

A closed immersion from the spectrum of a field identifies that field with
the residue field of its image.  This file packages the identification in the
ring-equivalence and additive-equivalence forms needed by the pointwise Ext
calculation.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-- The residue field at the image of the closed point of `Spec L` is
canonically isomorphic to `L`. -/
noncomputable def closedFieldPointResidueRingEquiv
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] :
    X.residueField (i (closedPoint (CommRingCat.of L))) ≃+* L := by
  let f : X.residueField (i (closedPoint (CommRingCat.of L))) →+* L :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo i)).hom
  apply RingEquiv.ofBijective f
  constructor
  · exact RingHom.injective f
  · intro y
    obtain ⟨a, ha⟩ :=
      ((ConcreteCategory.bijective_of_isIso
        (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of L)).hom).2.comp
        (i.stalkMap_surjective (closedPoint (CommRingCat.of L)))) y
    refine ⟨X.residue (i (closedPoint (CommRingCat.of L))) a, ?_⟩
    change Scheme.descResidueField (Scheme.stalkClosedPointTo i)
      (X.residue (i (closedPoint (CommRingCat.of L))) a) = y
    rw [← ConcreteCategory.comp_apply, Scheme.residue_descResidueField]
    exact ha

/-- Point-independent form of `closedFieldPointResidueRingEquiv`.  Since the
spectrum of a field has one point, the same equivalence applies at any
chosen representative of that point. -/
noncomputable def closedFieldPointResidueRingEquivAt
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) : X.residueField (i x) ≃+* L := by
  let h : i x = i (closedPoint (CommRingCat.of L)) :=
    congrArg i (Subsingleton.elim x (closedPoint (CommRingCat.of L)))
  exact ((X.residueFieldCongr h).commRingCatIsoToRingEquiv).trans
    (closedFieldPointResidueRingEquiv i)

end PfaffianDescent
