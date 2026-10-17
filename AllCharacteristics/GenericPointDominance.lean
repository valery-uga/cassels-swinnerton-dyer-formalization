import Mathlib.AlgebraicGeometry.Birational.Dominant

open TopologicalSpace CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- A field-valued point whose image is the generic point canonically gives
a homomorphism from the function field to its coefficient field. -/
noncomputable def Scheme.genericFieldPointRingHom
    {X : Scheme.{u}} [IrreducibleSpace X]
    {L : Type u} [Field L]
    (c : Spec (.of L) ⟶ X)
    (hc : c (IsLocalRing.closedPoint L) = genericPoint X) :
    X.functionField →+* L :=
  ((X.presheaf.stalkCongr (.of_eq hc.symm)).hom ≫
    Scheme.stalkClosedPointTo c).hom

/-- The function-field homomorphism associated to a generic field-valued
point factors that point through the canonical generic-point morphism. -/
theorem Scheme.genericFieldPointRingHom_spec
    {X : Scheme.{u}} [IrreducibleSpace X]
    {L : Type u} [Field L]
    (c : Spec (.of L) ⟶ X)
    (hc : c (IsLocalRing.closedPoint L) = genericPoint X) :
    Spec.map (CommRingCat.ofHom (X.genericFieldPointRingHom c hc)) ≫
      X.fromSpecStalk (genericPoint X) = c := by
  unfold Scheme.genericFieldPointRingHom
  change Spec.map
      ((X.presheaf.stalkCongr (.of_eq hc.symm)).hom ≫
        Scheme.stalkClosedPointTo c) ≫
      X.fromSpecStalk (genericPoint X) = c
  rw [Spec.map_comp, Category.assoc]
  have hcongr :
      Spec.map (X.presheaf.stalkCongr (.of_eq hc.symm)).hom ≫
          X.fromSpecStalk (genericPoint X) =
        X.fromSpecStalk (c (IsLocalRing.closedPoint L)) := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  rw [hcongr]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := c)

lemma Scheme.Hom.isDominant_of_genericPoint_eq
    {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) :
    IsDominant f := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply le_antisymm (Set.subset_univ _)
  calc
    Set.univ = closure {genericPoint Y} := (genericPoint_spec Y).symm
    _ ≤ closure (Set.range f) := closure_mono
      (Set.singleton_subset_iff.mpr ⟨genericPoint X, h⟩)

end AlgebraicGeometry

namespace AlgebraicGeometry

lemma Scheme.PartialMap.isDominant_hom_of_fromFunctionField_maps_generic
    {X Y : Scheme} [IsIntegral X] [IrreducibleSpace Y]
    (f : X.PartialMap Y)
    (h : f.fromFunctionField (genericPoint (Spec X.functionField)) = genericPoint Y) :
    IsDominant f.hom := by
  obtain ⟨x, hx⟩ := f.dense_domain.nonempty
  let _ : Nonempty f.domain := ⟨⟨x, hx⟩⟩
  let _ : IsIntegral f.domain := inferInstance
  apply Scheme.Hom.isDominant_of_genericPoint_eq
  let hxgen : genericPoint X ∈ f.domain :=
    (genericPoint_specializes _).mem_open f.domain.2
      f.dense_domain.nonempty.choose_spec
  let z : Spec (X.presheaf.stalk (genericPoint X)) :=
    IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))
  have hspec : genericPoint (Spec X.functionField) = z := by
    let _ : Unique (Spec (.of X.functionField)) := inferInstance
    exact Subsingleton.elim _ _
  have hpoint : f.domain.fromSpecStalkOfMem (genericPoint X) hxgen z =
      genericPoint f.domain := by
    apply f.domain.ι.isOpenEmbedding.injective
    have hcomp := congrArg (fun g : Spec (X.presheaf.stalk (genericPoint X)) ⟶ X => g z)
      (Scheme.Opens.fromSpecStalkOfMem_ι f.domain (genericPoint X) hxgen)
    have hbase : f.domain.ι
        (f.domain.fromSpecStalkOfMem (genericPoint X) hxgen z) = genericPoint X := by
      dsimp [z] at hcomp ⊢
      rw [Scheme.fromSpecStalk_closedPoint] at hcomp
      change f.domain.ι
        (f.domain.fromSpecStalkOfMem (genericPoint X) hxgen
          (IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)))) = genericPoint X at hcomp
      exact hcomp
    exact hbase.trans (genericPoint_eq_of_isOpenImmersion f.domain.ι).symm
  have hfrom : f.fromFunctionField (genericPoint (Spec X.functionField)) =
      f.hom (genericPoint f.domain) := by
    change (f.domain.fromSpecStalkOfMem (genericPoint X) hxgen ≫ f.hom)
        (genericPoint (Spec X.functionField)) = _
    rw [Scheme.Hom.comp_apply, hspec, hpoint]
  exact hfrom.symm.trans h

lemma Scheme.RationalMap.isDominant_of_fromFunctionField_maps_generic
    {X Y : Scheme} [IsIntegral X] [IrreducibleSpace Y]
    (f : X ⤏ Y)
    (h : f.fromFunctionField (genericPoint (Spec X.functionField)) = genericPoint Y) :
    f.IsDominant := by
  rw [← f.toRationalMap_representative,
    f.representative.isDominant_toRationalMap_iff]
  apply f.representative.isDominant_hom_of_fromFunctionField_maps_generic
  simpa only [← Scheme.RationalMap.fromFunctionField_toRationalMap f.representative,
    f.toRationalMap_representative] using h

end AlgebraicGeometry
