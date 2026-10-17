import PfaffianDescent.ThreeQuadricOTwoPairingIso
import PfaffianDescent.ThreeQuadricSheafKoszulExactness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! SOURCE ONLY / UNVERIFIED. Actual O(2)-tensor identifications of the
three displayed free terms, and exactness transported along those actual
term isomorphisms. The maps below are the transported SAME quadric maps.
The final ideal augmentation and its surjectivity remain separate. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "T2" => schemeModuleTensorRight (positiveSheafOfModules PS 2)

/-- The actual three unit sheaves, with their module category fixed. -/
abbrev threeQuadricOTwoUnitTriple : Fin 3 → (Proj PS).Modules :=
  fun _ => SheafOfModules.unit (Proj PS).ringCatSheaf

private local instance oTwoTensorTermsPreservesFiniteLimits : PreservesFiniteLimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 2 (by decide)
private local instance oTwoTensorTermsPreservesFiniteColimits : PreservesFiniteColimits T2 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 2 (by decide)

/-- The actual tensor of O(-4)^3, with the actual O(-2)^3. -/
def p3OTwoTensorNegativeFourTripleIso :
    (T2).obj (⨁ threeQuadricSheafTriple K 4) ≅
      ⨁ threeQuadricSheafTriple K 2 :=
  (T2).mapBiproduct (threeQuadricSheafTriple K 4) ≪≫
    biproduct.mapIso (fun _ : Fin 3 => p3OTwoTensorNegativeFourIso K)

/-- The actual tensor of O(-2)^3, with the actual structure-sheaf O^3. -/
def p3OTwoTensorNegativeTwoTripleIso :
    (T2).obj (⨁ threeQuadricSheafTriple K 2) ≅
      ⨁ threeQuadricOTwoUnitTriple K :=
  (T2).mapBiproduct (threeQuadricSheafTriple K 2) ≪≫
    biproduct.mapIso (fun _ : Fin 3 => p3OTwoTensorNegativeTwoIso K)

/-- The SAME first Koszul map after actual tensoring by O(2) and the
native mixed-pairing identifications, from O(-4) to O(-2)^3. -/
def threeQuadricOTwoKoszulFirst (f g h : PS 2) :
    sheafOfModules PS 4 ⟶ ⨁ threeQuadricSheafTriple K 2 :=
  (p3OTwoTensorNegativeSixIso K).inv ≫
    (T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
    (p3OTwoTensorNegativeFourTripleIso K).hom

/-- The SAME middle Koszul map after actual tensoring by O(2) and the
native mixed-pairing identifications, from O(-2)^3 to O^3. -/
def threeQuadricOTwoKoszulMiddle (f g h : PS 2) :
    (⨁ threeQuadricSheafTriple K 2) ⟶
      ⨁ threeQuadricOTwoUnitTriple K :=
  (p3OTwoTensorNegativeFourTripleIso K).inv ≫
    (T2).map (threeQuadricSheafKoszulMiddle K f g h) ≫
    (p3OTwoTensorNegativeTwoTripleIso K).hom

/-- Pure categorical cancellation, kept private so the actual functor-object
aliases never occur in the association/cancellation rewrite. -/
private theorem threeQuadricOTwo_conjugatedPair_zero
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B C A' B' C' : D}
    (eA : A ≅ A') (eB : B ≅ B') (eC : C ≅ C')
    (F : A ⟶ B) (G : B ⟶ C) (hFG : F ≫ G = 0) :
    (eA.inv ≫ F ≫ eB.hom) ≫ (eB.inv ≫ G ≫ eC.hom) = 0 := by
  calc
    (eA.inv ≫ F ≫ eB.hom) ≫ (eB.inv ≫ G ≫ eC.hom) =
        eA.inv ≫ F ≫ (eB.hom ≫ eB.inv ≫ G ≫ eC.hom) := by
      simp only [Category.assoc]
    _ = eA.inv ≫ F ≫ G ≫ eC.hom := by
      rw [eB.hom_inv_id_assoc]
    _ = eA.inv ≫ (F ≫ G) ≫ eC.hom := by
      simp only [Category.assoc]
    _ = 0 := by rw [hFG]; simp only [zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem threeQuadricOTwoKoszul_first_middle_zero (f g h : PS 2) :
    threeQuadricOTwoKoszulFirst K f g h ≫
      threeQuadricOTwoKoszulMiddle K f g h = 0 := by
  have hMapped :
      (T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
        (T2).map (threeQuadricSheafKoszulMiddle K f g h) = 0 := by
    calc
      (T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (T2).map (threeQuadricSheafKoszulMiddle K f g h) =
          (T2).map (threeQuadricSheafKoszulFirst K f g h ≫
            threeQuadricSheafKoszulMiddle K f g h) :=
        ((T2).map_comp (threeQuadricSheafKoszulFirst K f g h)
          (threeQuadricSheafKoszulMiddle K f g h)).symm
      _ = (T2).map (0 : sheafOfModules PS 6 ⟶ ⨁ threeQuadricSheafTriple K 2) :=
        congrArg (fun z : sheafOfModules PS 6 ⟶ ⨁ threeQuadricSheafTriple K 2 =>
          (T2).map z) (threeQuadricSheafKoszul_first_middle_zero K f g h)
      _ = 0 := (T2).map_zero _ _
  exact threeQuadricOTwo_conjugatedPair_zero
    (p3OTwoTensorNegativeSixIso K)
    (p3OTwoTensorNegativeFourTripleIso K)
    (p3OTwoTensorNegativeTwoTripleIso K)
    ((T2).map (threeQuadricSheafKoszulFirst K f g h))
    ((T2).map (threeQuadricSheafKoszulMiddle K f g h)) hMapped

/-- The literal displayed first three twists, with maps transported from
the actual untwisted Koszul complex rather than externally supplied. -/
def threeQuadricOTwoKoszul_firstMiddleShortComplex (f g h : PS 2) :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricOTwoKoszulFirst K f g h)
    (threeQuadricOTwoKoszulMiddle K f g h)
    (threeQuadricOTwoKoszul_first_middle_zero K f g h)

/-- An actual short-complex isomorphism from tensoring the original maps
to the literal displayed twists. -/
def threeQuadricOTwoKoszul_firstMiddleIso (f g h : PS 2) :
    (threeQuadricSheafKoszul_firstMiddleShortComplex K f g h).map T2 ≅
      threeQuadricOTwoKoszul_firstMiddleShortComplex K f g h :=
  ShortComplex.isoMk
    (p3OTwoTensorNegativeSixIso K)
    (p3OTwoTensorNegativeFourTripleIso K)
    (p3OTwoTensorNegativeTwoTripleIso K)
    (by
      change (p3OTwoTensorNegativeSixIso K).hom ≫
          (p3OTwoTensorNegativeSixIso K).inv ≫
            (T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
              (p3OTwoTensorNegativeFourTripleIso K).hom =
        (T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (p3OTwoTensorNegativeFourTripleIso K).hom
      exact (p3OTwoTensorNegativeSixIso K).hom_inv_id_assoc
        ((T2).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (p3OTwoTensorNegativeFourTripleIso K).hom))
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

/-- Exactness at the actual O(-2)^3 term. Finiteness and nonemptiness of
the SAME complete intersection supply all regularity hypotheses internally. -/
theorem threeQuadricOTwoKoszul_firstMiddle_exact
    (f g h : PS 2)
    [IsFinite (AllCharacteristics.HomogeneousProjective.toBase
      (R := K) (σ := Fin 4)
      (PfaffianDescent.tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (AllCharacteristics.HomogeneousProjective.scheme
      (R := K) (σ := Fin 4)
      (PfaffianDescent.tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))) :
    (threeQuadricOTwoKoszul_firstMiddleShortComplex K f g h).Exact := by
  apply ShortComplex.exact_of_iso (threeQuadricOTwoKoszul_firstMiddleIso K f g h)
  exact (threeQuadricSheafKoszul_firstMiddle_exact K f g h hT).map T2

end PfaffianDescent.ProjectiveNegativeTwist
