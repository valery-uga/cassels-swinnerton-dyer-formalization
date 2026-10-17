import PfaffianDescent.ThreeQuadricOTwoEntryNaturality
import PfaffianDescent.OriginalThreeQuadricOTwoResolution
import PfaffianDescent.P3HomogeneousGlobalSectionsLinear

/-! SOURCE ONLY / UNVERIFIED. The actual O(2)-twisted augmentation is the
row of genuine homogeneous quadric sections, on the SAME original ideal. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)
local notation "T2" => schemeModuleTensorRight (positiveSheafOfModules PS 2)
private local instance oTwoActualAugmentationPreservesFiniteLimits : PreservesFiniteLimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 2 (by decide)
private local instance oTwoActualAugmentationPreservesFiniteColimits : PreservesFiniteColimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 2 (by decide)
local notation "P2" => threeQuadricSheafTriple K 2
local notation "U3" => threeQuadricOTwoUnitTriple K

/-- Associate mapped composition in an abstract category before any
actual Proj sheaf dictionaries are specialized. -/
private theorem oTwoActualAugmentation_map_comp
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} {A B : D}
    (e : A ⟶ F.obj X) (a : X ⟶ Y) (b : Y ⟶ Z)
    (v : F.obj Z ⟶ B) :
    (e ≫ F.map a) ≫ F.map b ≫ v = e ≫ F.map (a ≫ b) ≫ v := by
  rw [F.map_comp]
  simp only [Category.assoc]

/-- The row argument is checked before the actual sheaf dictionaries
are specialized. All hypotheses here are derived internally at the caller. -/
private theorem oTwoActualAugmentation_biproduct_row
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {J : Type*} [Finite J]
    (F : C ⥤ D) (P : J → C) (Q : J → D)
    [HasBiproduct P] [HasBiproduct Q]
    {Z : C} {W : D}
    (a : (⨁ P) ⟶ Z) (e : (⨁ Q) ⟶ F.obj (⨁ P))
    (er : ∀ r, Q r ⟶ F.obj (P r)) (v : F.obj Z ⟶ W)
    (t : ∀ r, P r ⟶ Z) (row : ∀ r, Q r ⟶ W)
    (hi : ∀ r, biproduct.ι Q r ≫ e = er r ≫ F.map (biproduct.ι P r))
    (ht : ∀ r, biproduct.ι P r ≫ a = t r)
    (he : ∀ r, er r ≫ F.map (t r) ≫ v = row r) :
    e ≫ F.map a ≫ v = biproduct.desc row := by
  apply biproduct.hom_ext'
  intro r
  have hc : biproduct.ι Q r ≫ (e ≫ F.map a ≫ v) =
      er r ≫ F.map (biproduct.ι P r ≫ a) ≫ v := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ F.map a ≫ v) (hi r)).trans
        (oTwoActualAugmentation_map_comp F (er r) (biproduct.ι P r) a v))
  exact hc.trans
    ((congrArg (fun z => er r ≫ F.map z ≫ v) (ht r)).trans
      ((he r).trans (biproduct.ι_desc row r).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- No arbitrary rescaling of the scalar row: the unit-to-zero comparison
has literal section value 1, so the entry is exactly the section q. -/
theorem p3OTwoUnit_quadric_global_section (q : PS 2) :
    (p3OTwoUnitPositiveZeroIso K).hom ≫ positiveMulHomogeneous PS q 0 =
      p3HomogeneousGlobalSectionLinearMap K 2 q := by
  let e := schemeModuleGlobalSectionsLinearEquivOpenTop base
    (positiveSheafOfModules PS 2)
  apply e.injective
  change (positiveMulHomogeneous PS q 0).val.app (op ⊤)
      (((p3OTwoUnitPositiveZeroIso K).hom.val.app (op ⊤)) (1 : Γ(Proj PS, ⊤))) =
    e (e.symm (p3HomogeneousTopSectionLinearMap K 2 q))
  rw [e.apply_symm_apply]
  apply Subtype.ext
  funext x
  have hunit :
      (((p3OTwoUnitPositiveZeroIso K).hom.val.app (op ⊤))
        (1 : Γ(Proj PS, ⊤))).val x = (1 : PositiveFiber PS x.1) := by
    -- The two zero-twist comparisons retain the actual localization
    -- inclusion of the structure-sheaf section; that inclusion preserves 1.
    change (1 : HomogeneousLocalization.AtPrime PS (pointIdeal PS x.1)).val = 1
    exact HomogeneousLocalization.val_one
  have hq := positiveSectionValue_positiveGlobalSectionOfHomogeneous PS 2 q x.1
  change (p3HomogeneousTopSectionLinearMap K 2 q).val x =
    Localization.mk q.val (1 : (positivePointIdeal PS x.1).primeCompl) at hq
  change algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1) q.val *
      (((p3OTwoUnitPositiveZeroIso K).hom.val.app (op ⊤))
        (1 : Γ(Proj PS, ⊤))).val x =
    (p3HomogeneousTopSectionLinearMap K 2 q).val x
  exact (congrArg
    (fun z : PositiveFiber PS x.1 =>
      algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1) q.val * z)
    hunit).trans ((mul_one _).trans
      ((Localization.mk_one_eq_algebraMap _).symm.trans hq.symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma p3OTwoTensorNegativeTwoTripleIso_ι_inv (r : Fin 3) :
    biproduct.ι U3 r ≫ (p3OTwoTensorNegativeTwoTripleIso K).inv =
      (p3OTwoTensorNegativeTwoIso K).inv ≫ (T2).map (biproduct.ι P2 r) := by
  let E := p3OTwoTensorNegativeTwoIso K
  let V : Fin 3 → (Proj PS).Modules := fun r => (T2).obj (P2 r)
  let D := biproduct.desc (fun r : Fin 3 => (T2).map (biproduct.ι P2 r))
  have hi : biproduct.ι U3 r ≫ biproduct.map (fun _ : Fin 3 => E.inv) =
      E.inv ≫ biproduct.ι V r :=
    biproduct.ι_map (fun _ : Fin 3 => E.inv) r
  have hd : biproduct.ι V r ≫ D = (T2).map (biproduct.ι P2 r) :=
    biproduct.ι_desc (fun r : Fin 3 => (T2).map (biproduct.ι P2 r)) r
  change biproduct.ι U3 r ≫
      (biproduct.map (fun _ : Fin 3 => E.inv) ≫ D) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ D) hi).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t => E.inv ≫ t) hd)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem oTwoActualAugmentation_last_injection
    (f g h : PS 2) (r : Fin 3) :
    biproduct.ι P2 r ≫ threeQuadricSheafKoszulLast K f g h =
      ![mulHomogeneousToUnit PS f, mulHomogeneousToUnit PS g,
        mulHomogeneousToUnit PS h] r := by
  fin_cases r <;>
    simp [threeQuadricSheafKoszulLast, threeQuadricSheafKoszulLastZeroTwist,
      threeQuadricSheafMul, mulHomogeneousToUnit, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def oTwoActualAugmentation_quadric_entry (q : PS 2) :=
  (p3OTwoTensor_two_unit_quadric_entry (K := K) q).trans
    (p3OTwoUnit_quadric_global_section q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The SAME last Koszul row after O(2) tensoring is (f,g,h), with its
entries genuine morphism-valued H0(O(2)) sections. -/
theorem threeQuadricOTwoKoszulLast_ambient_eq_sum (f g h : PS 2) :
    (p3OTwoTensorNegativeTwoTripleIso K).inv ≫
      (T2).map (threeQuadricSheafKoszulLast K f g h) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
    biproduct.desc ![p3HomogeneousGlobalSectionLinearMap K 2 f,
      p3HomogeneousGlobalSectionLinearMap K 2 g,
      p3HomogeneousGlobalSectionLinearMap K 2 h] := by
  exact oTwoActualAugmentation_biproduct_row T2 P2 U3
    (threeQuadricSheafKoszulLast K f g h)
    (p3OTwoTensorNegativeTwoTripleIso K).inv
    (fun _ => (p3OTwoTensorNegativeTwoIso K).inv)
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom
    ![mulHomogeneousToUnit PS f, mulHomogeneousToUnit PS g,
      mulHomogeneousToUnit PS h]
    ![p3HomogeneousGlobalSectionLinearMap K 2 f,
      p3HomogeneousGlobalSectionLinearMap K 2 g,
      p3HomogeneousGlobalSectionLinearMap K 2 h]
    (fun r => p3OTwoTensorNegativeTwoTripleIso_ι_inv (K := K) r)
    (oTwoActualAugmentation_last_injection f g h)
    (by
      intro r
      fin_cases r
      · exact oTwoActualAugmentation_quadric_entry f
      · exact oTwoActualAugmentation_quadric_entry g
      · exact oTwoActualAugmentation_quadric_entry h)

-- SAME finite triple, original closed embedding and rank are declaration-local.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This equality fixes the actual scalar augmentation, not a substitute
isomorphism between polynomial spaces. -/
theorem p3OriginalThreeQuadricOTwoAugmentation_ambient_eq_sum
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8) :
    p3OriginalThreeQuadricOTwoAugmentation f g h l hZ ≫
      (closedImmersionIdealTwistSequence (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) (positiveSheafOfModules PS 2)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom =
    biproduct.desc ![p3HomogeneousGlobalSectionLinearMap K 2 f,
      p3HomogeneousGlobalSectionLinearMap K 2 g,
      p3HomogeneousGlobalSectionLinearMap K 2 h] := by
  change ((p3OTwoTensorNegativeTwoTripleIso K).inv ≫
    (T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) ≫
    (T2).map (IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))) ≫
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom = _
  let e := (p3OTwoTensorNegativeTwoTripleIso K).inv
  let a := p3OriginalThreeQuadricSheafAugmentation f g h l hZ
  let b := IdealSheafDataModule.closedImmersionModuleToUnit
    (l ≫ quotientProjMap (R := K) (σ := Fin 4)
      (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
  let v := (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 2)).hom
  have hm := oTwoActualAugmentation_map_comp T2 e a b v
  have ha := congrArg (fun t => e ≫ (T2).map t ≫ v)
    (p3OriginalThreeQuadricSheafAugmentation_comp f g h l hZ)
  exact hm.trans (ha.trans (threeQuadricOTwoKoszulLast_ambient_eq_sum f g h))

end PfaffianDescent
