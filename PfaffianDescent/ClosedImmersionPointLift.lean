import AllCharacteristics.CyclePushforward

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- A closed immersion identifies the residue field at a source point with
the residue field at its image.  Using the inverse residue-field map gives a
canonical field-valued lift of the image point back to the source. -/
noncomputable def closedImmersionResidueLift
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    Spec (Y.residueField (i x)) ⟶ X := by
  letI : IsIso (i.residueFieldMap x) :=
    AllCharacteristics.isIso_residueFieldMap_of_surjectiveOnStalks i x
  exact Spec.map (inv (i.residueFieldMap x)) ≫ X.fromSpecResidueField x

/-- The canonical residue-field lift through a closed immersion maps back to
the canonical residue-field point of the image. -/
theorem closedImmersionResidueLift_comp
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    closedImmersionResidueLift i x ≫ i =
      Y.fromSpecResidueField (i x) := by
  letI : IsIso (i.residueFieldMap x) :=
    AllCharacteristics.isIso_residueFieldMap_of_surjectiveOnStalks i x
  unfold closedImmersionResidueLift
  simp only [Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id,
    Category.id_comp]

/-- The chosen source point above a point known to lie in the range of a
closed immersion. -/
noncomputable def closedImmersionPointOfMemRange
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : S ⟶ Y) (s : S)
    (hs : f s ∈ Set.range i) : X :=
  hs.choose

theorem closedImmersionPointOfMemRange_spec
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : S ⟶ Y) (s : S)
    (hs : f s ∈ Set.range i) :
    i (closedImmersionPointOfMemRange i f s hs) = f s :=
  hs.choose_spec

/-- A pointwise range witness for a closed immersion canonically upgrades to
a morphism from the residue field of the source point into the closed
subscheme. -/
noncomputable def closedImmersionFieldPointLiftOfMemRange
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : S ⟶ Y) (s : S) (hs : f s ∈ Set.range i) :
    Spec (S.residueField s) ⟶ X :=
  let x := closedImmersionPointOfMemRange i f s hs
  let hx := closedImmersionPointOfMemRange_spec i f s hs
  Spec.map ((Y.residueFieldCongr hx).hom ≫ f.residueFieldMap s) ≫
    closedImmersionResidueLift i x

/-- The field-valued lift constructed from a range witness maps to the
canonical residue-field point followed by the original morphism. -/
theorem closedImmersionFieldPointLiftOfMemRange_comp
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : S ⟶ Y) (s : S) (hs : f s ∈ Set.range i) :
    closedImmersionFieldPointLiftOfMemRange i f s hs ≫ i =
      S.fromSpecResidueField s ≫ f := by
  let x := closedImmersionPointOfMemRange i f s hs
  let hx : i x = f s := closedImmersionPointOfMemRange_spec i f s hs
  unfold closedImmersionFieldPointLiftOfMemRange
  dsimp only
  rw [Category.assoc, closedImmersionResidueLift_comp]
  rw [Spec.map_comp, Category.assoc]
  rw [Scheme.residueFieldCongr_fromSpecResidueField hx]
  exact f.SpecMap_residueFieldMap_fromSpecResidueField s

/-- A point of the image of a closed immersion lifts to a closed point without
changing its residue degree over the common base. -/
theorem closedImmersion_closedPoint_lift
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ S)
    (y : closedPoints Y) (hy : y.1 ∈ Set.range i) :
    ∃ x : closedPoints X, i x.1 = y.1 ∧ (i ≫ f).residueDegree x.1 = f.residueDegree y.1 := by
  obtain ⟨x, hx⟩ := hy
  have he : i ⁻¹' {y.1} = {x} := by
    ext z
    change i z = y.1 ↔ z = x
    exact ⟨fun h => i.isClosedEmbedding.injective (h.trans hx.symm), fun h => h ▸ hx⟩
  have hclosed : IsClosed ({x} : Set X) := he ▸ y.2.preimage i.continuous
  have : IsIso (i.residueFieldMap x) :=
    AllCharacteristics.isIso_residueFieldMap_of_surjectiveOnStalks i x
  refine ⟨⟨x, hclosed⟩, hx, ?_⟩
  exact (AllCharacteristics.residueDegree_comp_of_residueFieldMap_isIso i f x).trans
    (congrArg f.residueDegree hx)

end PfaffianDescent
