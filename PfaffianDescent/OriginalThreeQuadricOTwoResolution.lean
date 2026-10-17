import PfaffianDescent.ThreeQuadricOTwoTensorTerms
import PfaffianDescent.OriginalThreeQuadricIdealAugmentation
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! SOURCE ONLY / UNVERIFIED. Both displayed sheaf resolutions for the
SAME original length-eight scheme. Every map is the actual quadric map or
its actual O(2)-tensor transport. The target is the actual original ideal
module tensor the actual positive twist, not a polynomial-space substitute. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "T2" => schemeModuleTensorRight (positiveSheafOfModules PS 2)
private local instance oTwoOriginalResolutionPreservesFiniteLimits : PreservesFiniteLimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 2 (by decide)
private local instance oTwoOriginalResolutionPreservesFiniteColimits : PreservesFiniteColimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 2 (by decide)
private theorem originalOTwo_conjugatedAugmentation_zero
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B C A' B' : D} (eA : A ≅ A') (eB : B ≅ B')
    (F : A ⟶ B) (G : B ⟶ C) (hFG : F ≫ G = 0) :
    (eA.inv ≫ F ≫ eB.hom) ≫ (eB.inv ≫ G) = 0 := by
  calc
    (eA.inv ≫ F ≫ eB.hom) ≫ (eB.inv ≫ G) =
        eA.inv ≫ F ≫ (eB.hom ≫ eB.inv ≫ G) := by
      simp only [Category.assoc]
    _ = eA.inv ≫ F ≫ G := by rw [eB.hom_inv_id_assoc]
    _ = eA.inv ≫ (F ≫ G) := by simp only [Category.assoc]
    _ = 0 := by rw [hFG]; exact comp_zero

-- Class search occurs in an abstract category, after the actual mapped
-- Epi/Mono has been obtained from the preservation theorem.
private theorem originalOTwo_isoInv_comp_epi
    {D : Type*} [Category D] {A B A' : D}
    (e : A ≅ A') (F : A ⟶ B) [Epi F] : Epi (e.inv ≫ F) := by
  infer_instance

private theorem originalOTwo_conjugated_mono
    {D : Type*} [Category D] {A B A' B' : D}
    (eA : A ≅ A') (eB : B ≅ B') (F : A ⟶ B) [Mono F] :
    Mono (eA.inv ≫ F ≫ eB.hom) := by
  infer_instance

-- SAME actual triple, closed immersion and rank inputs are declaration-local.

/-- Actual O^3 → I_originalZ(2), derived by tensoring the SAME
surjective three-quadric map. -/
def p3OriginalThreeQuadricOTwoAugmentation
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    (⨁ threeQuadricOTwoUnitTriple K) ⟶
      schemeModuleTensor (IdealSheafDataModule.closedImmersionModule (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)))
        (positiveSheafOfModules PS 2) :=
  (p3OTwoTensorNegativeTwoTripleIso K).inv ≫
    (T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem p3OriginalThreeQuadricOTwo_middle_augmentation_zero
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    threeQuadricOTwoKoszulMiddle K f g h ≫
      p3OriginalThreeQuadricOTwoAugmentation f g h l hZ = 0 := by
  have hMapped :
      (T2).map (threeQuadricSheafKoszulMiddle K f g h) ≫
        (T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) = 0 := by
    have hFG := p3OriginalThreeQuadricSheafKoszul_middle_augmentation_zero f g h l hZ
    exact ((T2).map_comp (threeQuadricSheafKoszulMiddle K f g h)
      (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)).symm.trans
        ((congrArg (fun z => (T2).map z) hFG).trans ((T2).map_zero _ _))
  exact originalOTwo_conjugatedAugmentation_zero
    (p3OTwoTensorNegativeFourTripleIso K)
    (p3OTwoTensorNegativeTwoTripleIso K)
    ((T2).map (threeQuadricSheafKoszulMiddle K f g h))
    ((T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) hMapped

/-- The literal last three terms O(-2)^3, O^3, I_originalZ(2). -/
def p3OriginalThreeQuadricOTwo_middleAugmentationShortComplex
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricOTwoKoszulMiddle K f g h)
    (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ)
    (p3OriginalThreeQuadricOTwo_middle_augmentation_zero f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def p3OriginalThreeQuadricOTwo_middleAugmentationIso
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    (p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex f g h l hZ).map T2 ≅
      p3OriginalThreeQuadricOTwo_middleAugmentationShortComplex f g h l hZ :=
  ShortComplex.isoMk
    (p3OTwoTensorNegativeFourTripleIso K)
    (p3OTwoTensorNegativeTwoTripleIso K)
    (Iso.refl _)
    (by
      change (p3OTwoTensorNegativeFourTripleIso K).hom ≫
          (p3OTwoTensorNegativeFourTripleIso K).inv ≫
            (T2).map (threeQuadricSheafKoszulMiddle K f g h) ≫
              (p3OTwoTensorNegativeTwoTripleIso K).hom =
        (T2).map (threeQuadricSheafKoszulMiddle K f g h) ≫
          (p3OTwoTensorNegativeTwoTripleIso K).hom
      exact (p3OTwoTensorNegativeFourTripleIso K).hom_inv_id_assoc
        ((T2).map (threeQuadricSheafKoszulMiddle K f g h) ≫
          (p3OTwoTensorNegativeTwoTripleIso K).hom))
    (by
      change (p3OTwoTensorNegativeTwoTripleIso K).hom ≫
          (p3OTwoTensorNegativeTwoTripleIso K).inv ≫
            (T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) =
        (T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) ≫ 𝟙 _
      exact ((p3OTwoTensorNegativeTwoTripleIso K).hom_inv_id_assoc
        ((T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))).trans
          (Category.comp_id
            ((T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))).symm)

/-- Genuine exactness at O^3 in the displayed twisted resolution. -/
theorem p3OriginalThreeQuadricOTwo_middleAugmentation_exact
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    (p3OriginalThreeQuadricOTwo_middleAugmentationShortComplex f g h l hZ).Exact := by
  apply ShortComplex.exact_of_iso
    (p3OriginalThreeQuadricOTwo_middleAugmentationIso f g h l hZ)
  exact (p3OriginalThreeQuadricSheafKoszul_middleAugmentation_exact f g h l hZ).map T2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual Epi onto the actual original I_Z(2). -/
theorem p3OriginalThreeQuadricOTwoAugmentation_epi
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    Epi (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ) := by
  letI : Epi (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) :=
    p3OriginalThreeQuadricSheafAugmentation_epi f g h l hZ
  letI : Epi ((T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) :=
    CategoryTheory.preserves_epi_of_preservesColimit (T2)
      (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)
  exact originalOTwo_isoInv_comp_epi (p3OTwoTensorNegativeTwoTripleIso K)
    ((T2).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact literal O(2)-twisted resolution over ANY field, for the SAME
closed rank-eight Z contained in the actual finite three-quadric intersection.
No exactness, coordinate comparison, cohomology or desired outcome input. -/
theorem p3OriginalThreeQuadricOTwo_displayed_resolution
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
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    Mono (threeQuadricOTwoKoszulFirst K f g h) ∧
    (threeQuadricOTwoKoszul_firstMiddleShortComplex K f g h).Exact ∧
    (p3OriginalThreeQuadricOTwo_middleAugmentationShortComplex f g h l hZ).Exact ∧
    Epi (p3OriginalThreeQuadricOTwoAugmentation f g h l hZ) := by
  have hbase := p3OriginalThreeQuadricSheafKoszul_displayed_resolution f g h l hZ
  letI : Mono (threeQuadricSheafKoszulFirst K f g h) := hbase.1
  letI : Mono ((T2).map (threeQuadricSheafKoszulFirst K f g h)) :=
    CategoryTheory.preserves_mono_of_preservesLimit (T2)
      (threeQuadricSheafKoszulFirst K f g h)
  have hmono : Mono (threeQuadricOTwoKoszulFirst K f g h) :=
    originalOTwo_conjugated_mono (p3OTwoTensorNegativeSixIso K)
      (p3OTwoTensorNegativeFourTripleIso K)
      ((T2).map (threeQuadricSheafKoszulFirst K f g h))
  have hT := p3ThreeQuadricOriginalLift_nonempty f g h l hZ
  exact ⟨hmono, threeQuadricOTwoKoszul_firstMiddle_exact K f g h hT,
    p3OriginalThreeQuadricOTwo_middleAugmentation_exact f g h l hZ,
    p3OriginalThreeQuadricOTwoAugmentation_epi f g h l hZ⟩

end PfaffianDescent.ProjectiveNegativeTwist
