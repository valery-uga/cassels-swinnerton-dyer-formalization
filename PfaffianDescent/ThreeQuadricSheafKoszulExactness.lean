import PfaffianDescent.ThreeQuadricSheafFractionStalkCoordinates
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! SOURCE ONLY / UNVERIFIED. Actual arbitrary-quadric sheaf exactness at
both middle terms, derived from internally proved homogeneous fraction
exactness and actual stalk squares, without an external exactness premise.
Identification of the image/cokernel with the ORIGINAL ideal sheaf remains
separate, as does tensor-by-O(3). -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local instance threeQuadricSheafExact_pointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- Actual first/middle short complex of the literal quadric twists. -/
def threeQuadricSheafKoszul_firstMiddleShortComplex (f g h : PS 2) : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricSheafKoszulFirst K f g h)
    (threeQuadricSheafKoszulMiddle K f g h)
    (threeQuadricSheafKoszul_first_middle_zero K f g h)

def threeQuadricSheafKoszul_middleLastZeroShortComplex (f g h : PS 2) : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricSheafKoszulMiddle K f g h)
    (threeQuadricSheafKoszulLastZeroTwist K f g h)
    (threeQuadricSheafKoszul_middle_lastZeroTwist_zero K f g h)

def threeQuadricSheafKoszul_middleLastShortComplex (f g h : PS 2) : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricSheafKoszulMiddle K f g h)
    (threeQuadricSheafKoszulLast K f g h)
    (threeQuadricSheafKoszul_middle_last_zero K f g h)

/-- Exactness of the actual first/middle categorical stalk maps. -/
theorem threeQuadricSheafKoszul_firstMiddle_stalk_exact
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
        f.val g.val h.val f.property g.property h.property)))
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulFirst K f g h))
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulMiddle K f g h)) := by
  have hf := homogeneousKoszulFraction_exact_of_finite (pointIdeal PS x)
    ⟨X j, isHomogeneous_X K j⟩ hx f g h hT
  have hlocal := LinearMap.exact_iff.mpr hf.1.symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := stalkAddEquivFractionModule PS 6 x)
    (e₂ := threeQuadricFraction_stalkTripleCoordinate K x 4)
    (e₃ := threeQuadricFraction_stalkTripleCoordinate K x 2)
    (g₁₂ := (homogeneousKoszulFractionFirst (pointIdeal PS x) f g h).toAddMonoidHom)
    (g₂₃ := (homogeneousKoszulFractionMiddle (pointIdeal PS x) f g h).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (threeQuadricFraction_first_stalk_coordinates K f g h x z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (threeQuadricFraction_middle_stalk_coordinates K f g h x z).symm

/-- Exactness of the actual middle/last categorical stalk maps. -/
theorem threeQuadricSheafKoszul_middleLastZero_stalk_exact
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
        f.val g.val h.val f.property g.property h.property)))
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulMiddle K f g h))
      ((schemeModuleStalkFunctor (Proj PS) x).map (threeQuadricSheafKoszulLastZeroTwist K f g h)) := by
  have hf := homogeneousKoszulFraction_exact_of_finite (pointIdeal PS x)
    ⟨X j, isHomogeneous_X K j⟩ hx f g h hT
  have hlocal := LinearMap.exact_iff.mpr hf.2.symm
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := threeQuadricFraction_stalkTripleCoordinate K x 4)
    (e₂ := threeQuadricFraction_stalkTripleCoordinate K x 2)
    (e₃ := stalkAddEquivFractionModule PS 0 x)
    (g₁₂ := (homogeneousKoszulFractionMiddle (pointIdeal PS x) f g h).toAddMonoidHom)
    (g₂₃ := (homogeneousKoszulFractionLast (pointIdeal PS x) f g h).toAddMonoidHom)
    (H := hlocal)
  · apply AddMonoidHom.ext
    intro z
    exact (threeQuadricFraction_middle_stalk_coordinates K f g h x z).symm
  · apply AddMonoidHom.ext
    intro z
    exact (threeQuadricFraction_last_stalk_coordinates K f g h x z).symm

private theorem threeQuadricSheaf_coordinateChart_exists (x : Proj PS) :
    ∃ j : Fin 4, X j ∈ (pointIdeal PS x).primeCompl := by
  have hx : x ∈ ⨆ i : Fin 4, p3StandardOpen (K := K) i := by
    rw [p3StandardOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨j, hj⟩

/-- Genuine sheaf exactness at O(-4)^3, internally derived. -/
theorem threeQuadricSheafKoszul_firstMiddle_exact
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
    (threeQuadricSheafKoszul_firstMiddleShortComplex K f g h).Exact := by
  let S : ShortComplex (SheafOfModules.{u} (Proj PS).ringCatSheaf) :=
    threeQuadricSheafKoszul_firstMiddleShortComplex K f g h
  let T : SheafOfModules.{u} (Proj PS).ringCatSheaf ⥤
      TopCat.Sheaf AddCommGrpCat.{u} (Proj PS) :=
    SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.Additive :=
    @SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf
      (TopologicalSpace.Opens (Proj PS)) inferInstance
      (Opens.grothendieckTopology (Proj PS))
      (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  letI : T.Faithful :=
    @SheafOfModules.instFaithfulSheafAddCommGrpCatToSheaf
      (TopologicalSpace.Opens (Proj PS)) inferInstance
      (Opens.grothendieckTopology (Proj PS))
      (Proj PS).ringCatSheaf
  apply T.reflects_exact_of_faithful S
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  letI : (schemeModuleStalkFunctor (Proj PS) x).Additive :=
    PfaffianDescent.instAdditiveModulesAddCommGrpCatSchemeModuleStalkFunctor
      (Proj PS) x
  letI : (schemeModuleStalkFunctor (Proj PS) x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (schemeModuleStalkFunctor (Proj PS) x)
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := threeQuadricSheaf_coordinateChart_exists K x
  exact threeQuadricSheafKoszul_firstMiddle_stalk_exact K f g h hT j x hj

/-- Genuine sheaf exactness at O(-2)^3, internally derived. -/
theorem threeQuadricSheafKoszul_middleLastZero_exact
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
    (threeQuadricSheafKoszul_middleLastZeroShortComplex K f g h).Exact := by
  let S : ShortComplex (SheafOfModules.{u} (Proj PS).ringCatSheaf) :=
    threeQuadricSheafKoszul_middleLastZeroShortComplex K f g h
  let T : SheafOfModules.{u} (Proj PS).ringCatSheaf ⥤
      TopCat.Sheaf AddCommGrpCat.{u} (Proj PS) :=
    SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.Additive :=
    @SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf
      (TopologicalSpace.Opens (Proj PS)) inferInstance
      (Opens.grothendieckTopology (Proj PS))
      (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  letI : T.Faithful :=
    @SheafOfModules.instFaithfulSheafAddCommGrpCatToSheaf
      (TopologicalSpace.Opens (Proj PS)) inferInstance
      (Opens.grothendieckTopology (Proj PS))
      (Proj PS).ringCatSheaf
  apply T.reflects_exact_of_faithful S
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  letI : (schemeModuleStalkFunctor (Proj PS) x).Additive :=
    PfaffianDescent.instAdditiveModulesAddCommGrpCatSchemeModuleStalkFunctor
      (Proj PS) x
  letI : (schemeModuleStalkFunctor (Proj PS) x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (schemeModuleStalkFunctor (Proj PS) x)
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  obtain ⟨j, hj⟩ := threeQuadricSheaf_coordinateChart_exists K x
  exact threeQuadricSheafKoszul_middleLastZero_stalk_exact K f g h hT j x hj

/-- Identifying actual O(0) with actual O does not alter exactness. -/
theorem threeQuadricSheafKoszul_middleLast_exact
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
    (threeQuadricSheafKoszul_middleLastShortComplex K f g h).Exact := by
  let e : threeQuadricSheafKoszul_middleLastZeroShortComplex K f g h ≅
      threeQuadricSheafKoszul_middleLastShortComplex K f g h :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (unitIsoZeroTwist PS).symm
      (by simp [threeQuadricSheafKoszul_middleLastZeroShortComplex,
        threeQuadricSheafKoszul_middleLastShortComplex])
      (by
        change (𝟙 _) ≫ threeQuadricSheafKoszulLastZeroTwist K f g h ≫
            (unitIsoZeroTwist PS).inv =
          threeQuadricSheafKoszulLastZeroTwist K f g h ≫ (unitIsoZeroTwist PS).inv
        exact Category.id_comp
          (threeQuadricSheafKoszulLastZeroTwist K f g h ≫ (unitIsoZeroTwist PS).inv))
  exact ShortComplex.exact_of_iso e
    (threeQuadricSheafKoszul_middleLastZero_exact K f g h hT)

end PfaffianDescent.ProjectiveNegativeTwist
