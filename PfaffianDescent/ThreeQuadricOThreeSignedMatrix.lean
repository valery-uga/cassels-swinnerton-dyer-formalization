import PfaffianDescent.ThreeQuadricNativeTwistedEntries

/-! SOURCE ONLY / UNVERIFIED. Conventional signed quadric expressions for
the SAME native tensor-transported Koszul maps; no matrix equality premise. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
-- Actual production exposed projective site/functor aliases in the diagrams.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The diagram is proved before substituting the actual projective sheaves. -/
private theorem nativeMappedBiproductIso_hom_π
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {J : Type*} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (A : J → C) [HasBiproduct A] [PreservesBiproduct A F]
    (B : J → D) [HasBiproduct B]
    (e : ∀ r, F.obj (A r) ≅ B r) (r : J) :
    ((F.mapBiproduct A) ≪≫ biproduct.mapIso e).hom ≫ biproduct.π B r =
      F.map (biproduct.π A r) ≫ (e r).hom := by
  calc
    _ = (F.mapBiproduct A).hom ≫
        (biproduct.π (F.obj ∘ A) r ≫ (e r).hom) := by
      rw [Iso.trans_hom, Category.assoc, biproduct.mapIso_hom, biproduct.map_π]
    _ = ((F.mapBiproduct A).hom ≫ biproduct.π (F.obj ∘ A) r) ≫
        (e r).hom := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [Functor.mapBiproduct_hom]
      exact congrArg (fun k => k ≫ (e r).hom)
        (biproduct.lift_π (f := F.obj ∘ A)
          (fun j => F.map (biproduct.π A j)) r)

private theorem nativeMappedBiproductIso_ι_inv
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {J : Type*} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (A : J → C) [HasBiproduct A] [PreservesBiproduct A F]
    (B : J → D) [HasBiproduct B]
    (e : ∀ r, F.obj (A r) ≅ B r) (r : J) :
    biproduct.ι B r ≫ ((F.mapBiproduct A) ≪≫ biproduct.mapIso e).inv =
      (e r).inv ≫ F.map (biproduct.ι A r) := by
  calc
    _ = ((e r).inv ≫ biproduct.ι (F.obj ∘ A) r) ≫
        (F.mapBiproduct A).inv := by
      rw [Iso.trans_inv, ← Category.assoc, biproduct.mapIso_inv, biproduct.ι_map]
    _ = (e r).inv ≫ (biproduct.ι (F.obj ∘ A) r ≫
        (F.mapBiproduct A).inv) := Category.assoc _ _ _
    _ = _ := by rw [Functor.mapBiproduct_inv, biproduct.ι_desc]

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "T3" => schemeModuleTensorRight (positiveSheafOfModules PS 3)
local instance : PreservesFiniteLimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 3 (by decide)
local instance : PreservesFiniteColimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 3 (by decide)
local notation "P1" => threeQuadricSheafTriple K 1
local notation "P2" => threeQuadricSheafTriple K 2
local notation "P4" => threeQuadricSheafTriple K 4
local notation "Q1" => (fun _ : Fin 3 => positiveSheafOfModules PS 1)

@[reassoc]
lemma p3OThreeTensorNegativeFourTripleIso_hom_π (r : Fin 3) :
    (p3OThreeTensorNegativeFourTripleIso K).hom ≫ biproduct.π P1 r =
      (T3).map (biproduct.π P4 r) ≫ (p3OThreeTensorNegativeFourIso K).hom := by
  simpa only [p3OThreeTensorNegativeFourTripleIso] using
    nativeMappedBiproductIso_hom_π (T3) P4 P1
      (fun _ : Fin 3 => p3OThreeTensorNegativeFourIso K) r

@[reassoc]
lemma p3OThreeTensorNegativeFourTripleIso_ι_inv (r : Fin 3) :
    biproduct.ι P1 r ≫ (p3OThreeTensorNegativeFourTripleIso K).inv =
      (p3OThreeTensorNegativeFourIso K).inv ≫ (T3).map (biproduct.ι P4 r) := by
  simpa only [p3OThreeTensorNegativeFourTripleIso] using
    nativeMappedBiproductIso_ι_inv (T3) P4 P1
      (fun _ : Fin 3 => p3OThreeTensorNegativeFourIso K) r

@[reassoc]
lemma p3OThreeTensorNegativeTwoTripleIso_hom_π (r : Fin 3) :
    (p3OThreeTensorNegativeTwoTripleIso K).hom ≫ biproduct.π Q1 r =
      (T3).map (biproduct.π P2 r) ≫ (p3OThreeTensorNegativeTwoIso K).hom := by
  simpa only [p3OThreeTensorNegativeTwoTripleIso] using
    nativeMappedBiproductIso_hom_π (T3) P2 Q1
      (fun _ : Fin 3 => p3OThreeTensorNegativeTwoIso K) r

@[reassoc]
lemma p3OThreeTensorNegativeTwoTripleIso_ι_inv (r : Fin 3) :
    biproduct.ι Q1 r ≫ (p3OThreeTensorNegativeTwoTripleIso K).inv =
      (p3OThreeTensorNegativeTwoIso K).inv ≫ (T3).map (biproduct.ι P2 r) := by
  simpa only [p3OThreeTensorNegativeTwoTripleIso] using
    nativeMappedBiproductIso_ι_inv (T3) P2 Q1
      (fun _ : Fin 3 => p3OThreeTensorNegativeTwoIso K) r

/-- The literal conventional first column (h,-g,f), on the actual twists. -/
theorem threeQuadricOThreeKoszulFirst_eq_signedColumn (f g h : PS 2) :
    threeQuadricOThreeKoszulFirst K f g h =
      biproduct.lift (f := P1) ![mulHomogeneous PS h 1,
        -mulHomogeneous PS g 1, mulHomogeneous PS f 1] := by
  apply biproduct.hom_ext
  intro r
  have hc : threeQuadricOThreeKoszulFirst K f g h ≫ biproduct.π P1 r =
      (p3OThreeTensorNegativeSixIso K).inv ≫
        (T3).map (threeQuadricSheafKoszulFirst K f g h ≫ biproduct.π P4 r) ≫
        (p3OThreeTensorNegativeFourIso K).hom := by
    simp only [threeQuadricOThreeKoszulFirst, Category.assoc,
      p3OThreeTensorNegativeFourTripleIso_hom_π, Functor.map_comp]
  rw [hc, biproduct.lift_π]
  fin_cases r <;>
    simp [threeQuadricSheafKoszulFirst, threeQuadricSheafMul,
      p3OThreeTensor_six_four_quadric_entry, Functor.map_neg]

/-- The conventional signed matrix, with rows indexed by input summands,
on actual negative O(-1) and positive O(1). -/
def threeQuadricOThreeConventionalMiddle (f g h : PS 2) : (⨁ P1) ⟶ ⨁ Q1 :=
  biproduct.matrix (f := P1) (g := Q1)
    ![![-negativeToPositiveMulHomogeneous PS g 1 (by decide),
      negativeToPositiveMulHomogeneous PS f 1 (by decide), 0],
      ![-negativeToPositiveMulHomogeneous PS h 1 (by decide), 0,
        negativeToPositiveMulHomogeneous PS f 1 (by decide)],
      ![0, -negativeToPositiveMulHomogeneous PS h 1 (by decide),
        negativeToPositiveMulHomogeneous PS g 1 (by decide)]]

/-- Fix one actual component square before expanding any of its signs. -/
private theorem p3OThreeKoszulMiddle_component_transport
    (f g h : PS 2) (r s : Fin 3) :
    biproduct.ι P1 r ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 s =
      (p3OThreeTensorNegativeFourIso K).inv ≫
        (T3).map (biproduct.ι P4 r ≫ threeQuadricSheafKoszulMiddle K f g h ≫
          biproduct.π P2 s) ≫ (p3OThreeTensorNegativeTwoIso K).hom := by
  simp only [threeQuadricOThreeKoszulMiddle, Category.assoc,
    p3OThreeTensorNegativeFourTripleIso_ι_inv_assoc,
    p3OThreeTensorNegativeTwoTripleIso_hom_π, Functor.map_comp]
  <;> simp only [Category.assoc]

private theorem p3OThreeKoszulMiddle_signed_entry_00
    (f g h : PS 2) :
    biproduct.ι P1 0 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 0 =
    biproduct.ι P1 0 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 0 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_01
    (f g h : PS 2) :
    biproduct.ι P1 0 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 1 =
    biproduct.ι P1 0 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 1 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_02
    (f g h : PS 2) :
    biproduct.ι P1 0 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 2 =
    biproduct.ι P1 0 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 2 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_10
    (f g h : PS 2) :
    biproduct.ι P1 1 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 0 =
    biproduct.ι P1 1 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 0 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_11
    (f g h : PS 2) :
    biproduct.ι P1 1 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 1 =
    biproduct.ι P1 1 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 1 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_12
    (f g h : PS 2) :
    biproduct.ι P1 1 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 2 =
    biproduct.ι P1 1 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 2 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_20
    (f g h : PS 2) :
    biproduct.ι P1 2 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 0 =
    biproduct.ι P1 2 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 0 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_21
    (f g h : PS 2) :
    biproduct.ι P1 2 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 1 =
    biproduct.ι P1 2 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 1 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

private theorem p3OThreeKoszulMiddle_signed_entry_22
    (f g h : PS 2) :
    biproduct.ι P1 2 ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 2 =
    biproduct.ι P1 2 ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 2 := by
  rw [p3OThreeKoszulMiddle_component_transport]
  simp [threeQuadricSheafKoszulMiddle, threeQuadricOThreeConventionalMiddle,
    threeQuadricSheafMul, p3OThreeTensor_four_two_quadric_entry, Functor.map_neg]

/-- Only finite index elimination remains here; all actual entries are opaque. -/
private theorem p3OThreeKoszulMiddle_signed_component
    (f g h : PS 2) (r s : Fin 3) :
    biproduct.ι P1 r ≫ threeQuadricOThreeKoszulMiddle K f g h ≫
      biproduct.π Q1 s =
    biproduct.ι P1 r ≫ threeQuadricOThreeConventionalMiddle K f g h ≫
      biproduct.π Q1 s := by
  fin_cases r <;> fin_cases s
  · exact p3OThreeKoszulMiddle_signed_entry_00 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_01 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_02 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_10 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_11 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_12 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_20 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_21 K f g h
  · exact p3OThreeKoszulMiddle_signed_entry_22 K f g h

/-- The native mixed-pairing identification gives exactly the conventional
signed quadric matrix, without row/column comparison certificates. -/
theorem threeQuadricOThreeKoszulMiddle_eq_signedMatrix (f g h : PS 2) :
    threeQuadricOThreeKoszulMiddle K f g h =
      threeQuadricOThreeConventionalMiddle K f g h := by
  apply biproduct.hom_ext'
  intro r
  apply biproduct.hom_ext
  intro s
  simpa only [Category.assoc] using
    p3OThreeKoszulMiddle_signed_component K f g h r s

/-- The actual ambient last map after twisting is the literal row (f,g,h)
of positive multiplication O(1)→O(3), with exact unit normalization. -/
theorem threeQuadricOThreeKoszulLast_ambient_eq_sum (f g h : PS 2) :
    (p3OThreeTensorNegativeTwoTripleIso K).inv ≫
      (T3).map (show (⨁ P2) ⟶ SheafOfModules.unit (Proj PS).ringCatSheaf from
        threeQuadricSheafKoszulLast K f g h) ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
    biproduct.desc (f := Q1) ![positiveMulHomogeneous PS f 1,
      positiveMulHomogeneous PS g 1, positiveMulHomogeneous PS h 1] := by
  apply biproduct.hom_ext'
  intro r
  have hc : biproduct.ι Q1 r ≫
      ((p3OThreeTensorNegativeTwoTripleIso K).inv ≫
        (T3).map (threeQuadricSheafKoszulLast K f g h) ≫
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom) =
      (p3OThreeTensorNegativeTwoIso K).inv ≫
        (T3).map (biproduct.ι P2 r ≫ threeQuadricSheafKoszulLast K f g h) ≫
        (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom := by
    simp only [Category.assoc, p3OThreeTensorNegativeTwoTripleIso_ι_inv_assoc,
      Functor.map_comp]
  rw [hc, biproduct.ι_desc]
  have he : biproduct.ι P2 r ≫ threeQuadricSheafKoszulLast K f g h =
      mulHomogeneousToUnit PS (![f, g, h] r) := by
    fin_cases r <;>
      simp [threeQuadricSheafKoszulLast, threeQuadricSheafKoszulLastZeroTwist,
        threeQuadricSheafMul, mulHomogeneousToUnit, Category.assoc]
  rw [he, p3OThreeTensor_two_unit_quadric_entry]
  fin_cases r <;> rfl

end PfaffianDescent.ProjectiveNegativeTwist
