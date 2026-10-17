import PfaffianDescent.TwistedCubicNativeGlobalLinearCoordinateImages
import PfaffianDescent.TwistedCubicNativeAmbientCoordinateImages
import PfaffianDescent.GroundTwistedCubicNativePositiveOnePullbackIso
import PfaffianDescent.ActualPositiveGradedHomogeneousSectionPullback

/-! SOURCE ONLY. Transport original coordinate maps using the SAME matrix
selected by the original ground presentation and SAME scheme parametrization.
The matrix/adjunct/linear-form image laws are proved, not supplied. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist ProjectiveLineNative
open BundleSectionZeroLocus
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Internally proved actual coordinate image of the SAME inverse ground
linear-coordinate Iso and its genuine positive-twist graded adjunct. -/
theorem projectiveLinearCoordinatePositiveTwistInvIso_coordinate
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (B J : HomogeneousIdeal PS)
    (hBJ : (J).toIdeal = (B).toIdeal.map (linearSubstitutionEquiv A hA).toRingHom)
    (i : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison
        (linearCoordinateChangeSchemeIso A hA B J hBJ).inv)
      (pullbackUnitComparison (linearCoordinateChangeSchemeIso A hA B J hBJ).inv) ≫
      (Scheme.Modules.pullback (linearCoordinateChangeSchemeIso A hA B J hBJ).inv).map
        ((positiveSheafOfModules (grading B) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading B) 1
            ⟨coordinate B i, coordinate_mem B i⟩)) ≫
      (projectiveLinearCoordinatePositiveTwistInvIso A hA B J hBJ 1).hom =
    (positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading J) 1
        ⟨Ideal.Quotient.mk (J).toIdeal (linearCoordinate A i),
          (quotientGradedRingHom J).2 (linearCoordinate_homogeneous A i)⟩) := by
  let f := linearCoordinateChangeGradedHom A hA B J hBJ
  have hsurj : Function.Surjective f :=
    (Ideal.quotientEquivAlg (B).toIdeal (J).toIdeal
      (linearSubstitutionEquiv A hA) hBJ).surjective
  let hf := gradedSurjective_irrelevant_le f hsurj
  let eta : grading B 1 := ⟨coordinate B i, coordinate_mem B i⟩
  have hImage : (⟨f eta, f.2 eta.property⟩ : grading J 1) =
      ⟨Ideal.Quotient.mk (J).toIdeal (linearCoordinate A i),
        (quotientGradedRingHom J).2 (linearCoordinate_homogeneous A i)⟩ := by
    apply Subtype.ext
    change Ideal.quotientEquivAlg (B).toIdeal (J).toIdeal
      (linearSubstitutionEquiv A hA) hBJ (Ideal.Quotient.mk (B).toIdeal (X i)) = _
    rw [Ideal.quotientEquivAlg_mk]
    exact congrArg (Ideal.Quotient.mk (J).toIdeal) (linearSubstitution_X A i)
  have h := actualPositiveGradedHomogeneousSection_pullback
    (grading B) (grading J) f hf 1 eta
  exact h.trans (congrArg (fun q : grading J 1 =>
    (positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading J) 1 q)) hImage)

/-- The SAME composite normalized pullback and actual composite Iso send
an actual ambient section to its iterated pullback. Scheme/module arguments
remain abstract during all Iso-hom and pullback-composition conversion. -/
private theorem groundActualComposedIso_sectionImageCut
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Z.Modules) (Q' : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback g).obj Q ≅ Q')
    (a : (Scheme.Modules.pullback f).obj Q' ≅ N)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ Q)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ Q')
    (h : CategoryTheory.inv («I» := isIso_pullbackUnitComparison g)
        (pullbackUnitComparison g) ≫ (Scheme.Modules.pullback g).map s ≫ e.hom = t) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
        (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      ((Scheme.Modules.pullbackComp f g).symm.app Q ≪≫
        (Scheme.Modules.pullback f).mapIso e ≪≫ a).hom =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
        (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map t ≫ a.hom := by
  have hc := nativeNormalizedPullbackSectionMap_comp_coefficient f g Q Q' s e.hom
  change CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
      (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app Q ≫
      (Scheme.Modules.pullback f).map e.hom ≫ a.hom = _
  have hc' : CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
      (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app Q ≫
      (Scheme.Modules.pullback f).map e.hom ≫ a.hom =
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison f) (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map
          (CategoryTheory.inv («I» := isIso_pullbackUnitComparison g) (pullbackUnitComparison g) ≫
            (Scheme.Modules.pullback g).map s ≫ e.hom) ≫ a.hom := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ a.hom) hc
  exact hc'.trans
    (congrArg (fun z =>
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison f) (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map z ≫ a.hom) h)

/-- Exact image law for an ordinary ground matrix presentation, before
the existing presentation's SAME chosen matrix is substituted. -/
theorem groundMatrixTwistedCubicNativePositiveOne_coordinate
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det)
    (B : HomogeneousIdeal PS)
    (hBI : (I).toIdeal = (B).toIdeal.map (linearSubstitutionEquiv A hA).toRingHom)
    (i : Fin 4) :
    let e := linearCoordinateChangeSchemeIso A hA B I hBI
    let v := standardProjectiveLineToTwistedCubic (K := K)
    let T := positiveSheafOfModules (grading B) 1
    let E := (Scheme.Modules.pullbackComp v e.inv).symm.app T ≪≫
      (Scheme.Modules.pullback v).mapIso
        (projectiveLinearCoordinatePositiveTwistInvIso A hA B I hBI 1) ≪≫
      standardTwistedCubicNativePositiveOnePullbackIso (K := K)
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (v ≫ e.inv))
      (pullbackUnitComparison (v ≫ e.inv)) ≫
      (Scheme.Modules.pullback (v ≫ e.inv)).map
        (T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading B) 1
          ⟨coordinate B i, coordinate_mem B i⟩)) ≫ E.hom =
    (positiveSheafOfModules (grading L) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading L) 3
        (actualLineHomogeneousQuotientPiece K 3
          (standardTwistedCubicLiteralLineLinearPolynomial (K := K) A i))) := by
  dsimp only
  exact (groundActualComposedIso_sectionImageCut
    (standardProjectiveLineToTwistedCubic (K := K))
    (linearCoordinateChangeSchemeIso A hA B I hBI).inv
    (positiveSheafOfModules (grading B) 1) (positiveSheafOfModules (grading I) 1)
    (positiveSheafOfModules (grading L) 3)
    (projectiveLinearCoordinatePositiveTwistInvIso A hA B I hBI 1)
    (standardTwistedCubicNativePositiveOnePullbackIso (K := K))
    ((positiveSheafOfModules (grading B) 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading B) 1
        ⟨coordinate B i, coordinate_mem B i⟩))
    ((positiveSheafOfModules (grading I) 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 1
        ⟨Ideal.Quotient.mk (I).toIdeal (linearCoordinate A i),
          (quotientGradedRingHom I).2 (linearCoordinate_homogeneous A i)⟩))
    (projectiveLinearCoordinatePositiveTwistInvIso_coordinate (K := K) A hA B I hBI i)).trans
      (standardTwistedCubicNativePositiveOnePullbackIso_linearCoordinate_hom (K := K) A i)

/-- Literal cubic-section map under EXACT matrix selected by the original
GroundTwistedCubicPresentation; no second coordinate choice is made. -/
def GroundTwistedCubicPresentation.literalChosenNativeCubicSectionHom
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    SheafOfModules.unit (scheme L).ringCatSheaf ⟶ positiveSheafOfModules (grading L) 3 :=
  let A : GL (Fin 4) K := Classical.choose hB
  (positiveSheafOfModules (grading L) 3).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous (grading L) 3
      (actualLineHomogeneousQuotientPiece K 3
        (standardTwistedCubicLiteralLineLinearPolynomial (K := K)
          (A : Matrix (Fin 4) (Fin 4) K) i)))

/-- SAME chosen ground matrix, SAME original curve-to-P1 Iso inverse,
SAME native bundle comparison: every original coordinate has literal image. -/
theorem GroundTwistedCubicPresentation.nativePositiveOnePullbackIso_coordinate
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison hB.schemeIsoProjectiveLine.inv)
        (pullbackUnitComparison hB.schemeIsoProjectiveLine.inv) ≫
      (Scheme.Modules.pullback hB.schemeIsoProjectiveLine.inv).map
        ((positiveSheafOfModules (grading B) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading B) 1
            ⟨coordinate B i, coordinate_mem B i⟩)) ≫
      hB.nativePositiveOnePullbackIso.hom = hB.literalChosenNativeCubicSectionHom i := by
  let A : GL (Fin 4) K := Classical.choose hB
  have hA : IsUnit ((A : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)
  have hAB : (B).toIdeal.map
      (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K := Classical.choose_spec hB
  have hBI : (I).toIdeal = (B).toIdeal.map
      (linearSubstitutionEquiv (A : Matrix (Fin 4) (Fin 4) K) hA).toRingHom := hAB.symm
  exact groundMatrixTwistedCubicNativePositiveOne_coordinate
    (A : Matrix (Fin 4) (Fin 4) K) hA B hBI i

/-- Whole original ambient-coordinate image under SAME chosen ground
parametrization and SAME native ambient comparison, with no image premise. -/
theorem GroundTwistedCubicPresentation.nativeAmbientPositiveOnePullbackIso_coordinate
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    actualLineAmbientPulledCoordinateHom
        (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B) i ≫
      hB.nativeAmbientPositiveOnePullbackIso.hom =
    hB.literalChosenNativeCubicSectionHom i := by
  exact (groundActualComposedIso_sectionImageCut
    hB.schemeIsoProjectiveLine.inv (quotientProjMap B)
    (positiveSheafOfModules PS 1) (positiveSheafOfModules (grading B) 1)
    (positiveSheafOfModules (grading L) 3)
    (actualAmbientPositiveTwistQuotientIso B 1) hB.nativePositiveOnePullbackIso
    ((positiveSheafOfModules PS 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous PS 1 ⟨X i, isHomogeneous_X K i⟩))
    ((positiveSheafOfModules (grading B) 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading B) 1
        ⟨coordinate B i, coordinate_mem B i⟩))
    (actualAmbientPositiveTwistQuotientIso_homogeneousSection B 1
      ⟨X i, isHomogeneous_X K i⟩)).trans
        (hB.nativePositiveOnePullbackIso_coordinate i)

end PfaffianDescent.QuarticNet
