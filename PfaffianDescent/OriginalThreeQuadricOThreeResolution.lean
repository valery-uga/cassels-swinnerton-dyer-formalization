import PfaffianDescent.ThreeQuadricOThreeTensorTerms
import PfaffianDescent.OriginalThreeQuadricIdealAugmentation
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! SOURCE ONLY / UNVERIFIED. Both displayed sheaf resolutions for the
SAME original length-eight scheme. Every map is the actual quadric map or
its actual O(3)-tensor transport. The target is the actual original ideal
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
local notation "T3" => schemeModuleTensorRight (positiveSheafOfModules PS 3)
local instance : PreservesFiniteLimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 3 (by decide)
local instance : PreservesFiniteColimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 3 (by decide)
-- Actual triple/closed immersion/rank inputs are bound at each declaration.

-- Same abstract cancellation used by the accepted tensor-term proof,
-- with the ideal target unchanged rather than a further target Iso.
private theorem originalOThree_conjugatedAugmentation_zero
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
private theorem originalOThree_isoInv_comp_epi
    {D : Type*} [Category D] {A B A' : D}
    (e : A ≅ A') (F : A ⟶ B) [Epi F] : Epi (e.inv ≫ F) := by
  infer_instance

private theorem originalOThree_conjugated_mono
    {D : Type*} [Category D] {A B A' B' : D}
    (eA : A ≅ A') (eB : B ≅ B') (F : A ⟶ B) [Mono F] :
    Mono (eA.inv ≫ F ≫ eB.hom) := by
  infer_instance

/-- Actual O(1)^3 → I_originalZ(3), derived by tensoring the SAME
surjective three-quadric map. -/
def p3OriginalThreeQuadricOThreeAugmentation
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
    (⨁ (fun _ : Fin 3 => positiveSheafOfModules PS 1)) ⟶
      schemeModuleTensor (IdealSheafDataModule.closedImmersionModule (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)))
        (positiveSheafOfModules PS 3) :=
  (p3OThreeTensorNegativeTwoTripleIso K).inv ≫
    (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem p3OriginalThreeQuadricOThree_middle_augmentation_zero
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
    threeQuadricOThreeKoszulMiddle K f g h ≫
      p3OriginalThreeQuadricOThreeAugmentation f g h l hZ = 0 := by
  have hMapped :
      (T3).map (threeQuadricSheafKoszulMiddle K f g h) ≫
        (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) = 0 := by
    have hFG := p3OriginalThreeQuadricSheafKoszul_middle_augmentation_zero f g h l hZ
    exact ((T3).map_comp (threeQuadricSheafKoszulMiddle K f g h)
      (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)).symm.trans
        ((congrArg (fun z => (T3).map z) hFG).trans ((T3).map_zero _ _))
  exact originalOThree_conjugatedAugmentation_zero
    (p3OThreeTensorNegativeFourTripleIso K)
    (p3OThreeTensorNegativeTwoTripleIso K)
    ((T3).map (threeQuadricSheafKoszulMiddle K f g h))
    ((T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) hMapped

/-- The literal last three terms O(-1)^3, O(1)^3, I_originalZ(3). -/
def p3OriginalThreeQuadricOThree_middleAugmentationShortComplex
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
  ShortComplex.mk (threeQuadricOThreeKoszulMiddle K f g h)
    (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ)
    (p3OriginalThreeQuadricOThree_middle_augmentation_zero f g h l hZ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def p3OriginalThreeQuadricOThree_middleAugmentationIso
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
    (p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex f g h l hZ).map T3 ≅
      p3OriginalThreeQuadricOThree_middleAugmentationShortComplex f g h l hZ :=
  ShortComplex.isoMk
    (p3OThreeTensorNegativeFourTripleIso K)
    (p3OThreeTensorNegativeTwoTripleIso K)
    (Iso.refl _)
    (by
      change (p3OThreeTensorNegativeFourTripleIso K).hom ≫
          (p3OThreeTensorNegativeFourTripleIso K).inv ≫
            (T3).map (threeQuadricSheafKoszulMiddle K f g h) ≫
              (p3OThreeTensorNegativeTwoTripleIso K).hom =
        (T3).map (threeQuadricSheafKoszulMiddle K f g h) ≫
          (p3OThreeTensorNegativeTwoTripleIso K).hom
      exact (p3OThreeTensorNegativeFourTripleIso K).hom_inv_id_assoc
        ((T3).map (threeQuadricSheafKoszulMiddle K f g h) ≫
          (p3OThreeTensorNegativeTwoTripleIso K).hom))
    (by
      change (p3OThreeTensorNegativeTwoTripleIso K).hom ≫
          (p3OThreeTensorNegativeTwoTripleIso K).inv ≫
            (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) =
        (T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) ≫ 𝟙 _
      exact ((p3OThreeTensorNegativeTwoTripleIso K).hom_inv_id_assoc
        ((T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))).trans
          (Category.comp_id
            ((T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))).symm)

/-- Genuine exactness at O(1)^3 in the displayed twisted resolution. -/
theorem p3OriginalThreeQuadricOThree_middleAugmentation_exact
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
    (p3OriginalThreeQuadricOThree_middleAugmentationShortComplex f g h l hZ).Exact := by
  apply ShortComplex.exact_of_iso
    (p3OriginalThreeQuadricOThree_middleAugmentationIso f g h l hZ)
  exact (p3OriginalThreeQuadricSheafKoszul_middleAugmentation_exact f g h l hZ).map T3

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual Epi onto the actual original I_Z(3). -/
theorem p3OriginalThreeQuadricOThreeAugmentation_epi
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
    Epi (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ) := by
  letI : Epi (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) :=
    p3OriginalThreeQuadricSheafAugmentation_epi f g h l hZ
  letI : Epi ((T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)) :=
    CategoryTheory.preserves_epi_of_preservesColimit (T3)
      (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)
  exact originalOThree_isoInv_comp_epi (p3OThreeTensorNegativeTwoTripleIso K)
    ((T3).map (p3OriginalThreeQuadricSheafAugmentation f g h l hZ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact literal O(3)-twisted resolution over ANY field, for the SAME
closed rank-eight Z contained in the actual finite three-quadric intersection.
No exactness, coordinate comparison, cohomology or desired outcome input. -/
theorem p3OriginalThreeQuadricOThree_displayed_resolution
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
    Mono (threeQuadricOThreeKoszulFirst K f g h) ∧
    (threeQuadricOThreeKoszul_firstMiddleShortComplex K f g h).Exact ∧
    (p3OriginalThreeQuadricOThree_middleAugmentationShortComplex f g h l hZ).Exact ∧
    Epi (p3OriginalThreeQuadricOThreeAugmentation f g h l hZ) := by
  have hbase := p3OriginalThreeQuadricSheafKoszul_displayed_resolution f g h l hZ
  letI : Mono (threeQuadricSheafKoszulFirst K f g h) := hbase.1
  letI : Mono ((T3).map (threeQuadricSheafKoszulFirst K f g h)) :=
    CategoryTheory.preserves_mono_of_preservesLimit (T3)
      (threeQuadricSheafKoszulFirst K f g h)
  have hmono : Mono (threeQuadricOThreeKoszulFirst K f g h) :=
    originalOThree_conjugated_mono (p3OThreeTensorNegativeSixIso K)
      (p3OThreeTensorNegativeFourTripleIso K)
      ((T3).map (threeQuadricSheafKoszulFirst K f g h))
  have hT := p3ThreeQuadricOriginalLift_nonempty f g h l hZ
  exact ⟨hmono, threeQuadricOThreeKoszul_firstMiddle_exact K f g h hT,
    p3OriginalThreeQuadricOThree_middleAugmentation_exact f g h l hZ,
    p3OriginalThreeQuadricOThreeAugmentation_epi f g h l hZ⟩

end PfaffianDescent.ProjectiveNegativeTwist
