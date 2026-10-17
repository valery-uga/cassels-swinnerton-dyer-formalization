import PfaffianDescent.ThreeQuadricOThreePairingIso
import PfaffianDescent.ThreeQuadricSheafKoszulExactness
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! SOURCE ONLY / UNVERIFIED. Actual O(3)-tensor identifications of the
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
local notation "T3" => schemeModuleTensorRight (positiveSheafOfModules PS 3)

local instance : PreservesFiniteLimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteLimits K 3 (by decide)
local instance : PreservesFiniteColimits T3 :=
  p3PositiveTwist_tensorRight_preservesFiniteColimits K 3 (by decide)

/-- The actual tensor of O(-4)^3, with the actual O(-1)^3. -/
def p3OThreeTensorNegativeFourTripleIso :
    (T3).obj (⨁ threeQuadricSheafTriple K 4) ≅
      ⨁ threeQuadricSheafTriple K 1 :=
  (T3).mapBiproduct (threeQuadricSheafTriple K 4) ≪≫
    biproduct.mapIso (fun _ : Fin 3 => p3OThreeTensorNegativeFourIso K)

/-- The actual tensor of O(-2)^3, with the actual positive O(1)^3. -/
def p3OThreeTensorNegativeTwoTripleIso :
    (T3).obj (⨁ threeQuadricSheafTriple K 2) ≅
      ⨁ (fun _ : Fin 3 => positiveSheafOfModules PS 1) :=
  (T3).mapBiproduct (threeQuadricSheafTriple K 2) ≪≫
    biproduct.mapIso (fun _ : Fin 3 => p3OThreeTensorNegativeTwoIso K)

/-- The SAME first Koszul map after actual tensoring by O(3) and the
native mixed-pairing identifications, from O(-3) to O(-1)^3. -/
def threeQuadricOThreeKoszulFirst (f g h : PS 2) :
    sheafOfModules PS 3 ⟶ ⨁ threeQuadricSheafTriple K 1 :=
  (p3OThreeTensorNegativeSixIso K).inv ≫
    (T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
    (p3OThreeTensorNegativeFourTripleIso K).hom

/-- The SAME middle Koszul map after actual tensoring by O(3) and the
native mixed-pairing identifications, from O(-1)^3 to O(1)^3. -/
def threeQuadricOThreeKoszulMiddle (f g h : PS 2) :
    (⨁ threeQuadricSheafTriple K 1) ⟶
      ⨁ (fun _ : Fin 3 => positiveSheafOfModules PS 1) :=
  (p3OThreeTensorNegativeFourTripleIso K).inv ≫
    (T3).map (threeQuadricSheafKoszulMiddle K f g h) ≫
    (p3OThreeTensorNegativeTwoTripleIso K).hom

/-- Pure categorical cancellation, kept private so the actual functor-object
aliases never occur in the association/cancellation rewrite. -/
private theorem threeQuadricOThree_conjugatedPair_zero
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
theorem threeQuadricOThreeKoszul_first_middle_zero (f g h : PS 2) :
    threeQuadricOThreeKoszulFirst K f g h ≫
      threeQuadricOThreeKoszulMiddle K f g h = 0 := by
  have hMapped :
      (T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
        (T3).map (threeQuadricSheafKoszulMiddle K f g h) = 0 := by
    calc
      (T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (T3).map (threeQuadricSheafKoszulMiddle K f g h) =
          (T3).map (threeQuadricSheafKoszulFirst K f g h ≫
            threeQuadricSheafKoszulMiddle K f g h) :=
        ((T3).map_comp (threeQuadricSheafKoszulFirst K f g h)
          (threeQuadricSheafKoszulMiddle K f g h)).symm
      _ = (T3).map (0 : sheafOfModules PS 6 ⟶ ⨁ threeQuadricSheafTriple K 2) :=
        congrArg (fun z : sheafOfModules PS 6 ⟶ ⨁ threeQuadricSheafTriple K 2 =>
          (T3).map z) (threeQuadricSheafKoszul_first_middle_zero K f g h)
      _ = 0 := (T3).map_zero _ _
  exact threeQuadricOThree_conjugatedPair_zero
    (p3OThreeTensorNegativeSixIso K)
    (p3OThreeTensorNegativeFourTripleIso K)
    (p3OThreeTensorNegativeTwoTripleIso K)
    ((T3).map (threeQuadricSheafKoszulFirst K f g h))
    ((T3).map (threeQuadricSheafKoszulMiddle K f g h)) hMapped

/-- The literal displayed first three twists, with maps transported from
the actual untwisted Koszul complex rather than externally supplied. -/
def threeQuadricOThreeKoszul_firstMiddleShortComplex (f g h : PS 2) :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricOThreeKoszulFirst K f g h)
    (threeQuadricOThreeKoszulMiddle K f g h)
    (threeQuadricOThreeKoszul_first_middle_zero K f g h)

/-- An actual short-complex isomorphism from tensoring the original maps
to the literal displayed twists. -/
def threeQuadricOThreeKoszul_firstMiddleIso (f g h : PS 2) :
    (threeQuadricSheafKoszul_firstMiddleShortComplex K f g h).map T3 ≅
      threeQuadricOThreeKoszul_firstMiddleShortComplex K f g h :=
  ShortComplex.isoMk
    (p3OThreeTensorNegativeSixIso K)
    (p3OThreeTensorNegativeFourTripleIso K)
    (p3OThreeTensorNegativeTwoTripleIso K)
    (by
      change (p3OThreeTensorNegativeSixIso K).hom ≫
          (p3OThreeTensorNegativeSixIso K).inv ≫
            (T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
              (p3OThreeTensorNegativeFourTripleIso K).hom =
        (T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (p3OThreeTensorNegativeFourTripleIso K).hom
      exact (p3OThreeTensorNegativeSixIso K).hom_inv_id_assoc
        ((T3).map (threeQuadricSheafKoszulFirst K f g h) ≫
          (p3OThreeTensorNegativeFourTripleIso K).hom))
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

/-- Exactness at the actual O(-1)^3 term. Finiteness and nonemptiness of
the SAME complete intersection supply all regularity hypotheses internally. -/
theorem threeQuadricOThreeKoszul_firstMiddle_exact
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
    (threeQuadricOThreeKoszul_firstMiddleShortComplex K f g h).Exact := by
  apply ShortComplex.exact_of_iso (threeQuadricOThreeKoszul_firstMiddleIso K f g h)
  exact (threeQuadricSheafKoszul_firstMiddle_exact K f g h hT).map T3

end PfaffianDescent.ProjectiveNegativeTwist
