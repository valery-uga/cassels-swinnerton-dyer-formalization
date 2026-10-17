import PfaffianDescent.GroundTwistedCubicNativeCoordinateImages
import PfaffianDescent.QuarticExceptionalNativeCubicHZeroBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! SOURCE ONLY. The ORIGINAL ground parametrization's four ambient
coordinate maps form a basis of its GENUINE native pullback H0. The SAME
chosen GL matrix and checked native O1→O3/image laws supply every step. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist ProjectiveLineNative
open BundleSectionZeroLocus
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "N" => positiveSheafOfModules (grading L) 3
local notation "Hthree" => SchemeModuleGlobalSectionsOver (toBase L) N

/-- SAME canonical native H0 structures; imported private instances are
not relied on for downstream instance inference. -/
private noncomputable instance completeSeriesNativeHZeroAddCommGroup
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    AddCommGroup (SchemeModuleGlobalSectionsOver p Q) :=
  instAddCommGroupSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

private noncomputable instance completeSeriesNativeHZeroModule
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    Module K (SchemeModuleGlobalSectionsOver p Q) :=
  instModuleSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

/-- Literal matrix row coefficients give precisely the ORIGINAL standard
parametrization of the original linear coordinate, as actual polynomials. -/
private theorem originalMatrixRow_binaryCubicCut
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    binaryForm 3 (A i) = standardTwistedCubicParam K (linearCoordinate A i) := by
  change binaryForm 3 (fun j : Fin 4 => A i j) =
    standardTwistedCubicParam K (∑ j : Fin 4, C (A i j) * X j)
  rw [map_sum]
  simp [binaryForm, binaryExponent, standardTwistedCubicParam,
    Fin.sum_univ_four, monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_two,
    Finsupp.single_apply] <;> ring

/-- Public checked binary-coefficient H0 equivalence retains its literal
section value. No new homogeneous-piece-as-H0 identification is chosen. -/
private theorem nativeBinaryCoefficients_literalSectionCut (q : Fin 4 → K) :
    binaryCubicCoefficientsNativeHZeroLinearEquiv (K := K) q =
    (N).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading L) 3
        (actualLineHomogeneousQuotientPiece K 3
          ⟨rename finTwoEquiv (binaryForm 3 q),
            (binaryForm_homogeneous 3 q).rename_isHomogeneous⟩)) := by
  exact binaryCubicNativeHZeroLinearEquiv_apply (K := K)
    ⟨binaryForm 3 q, binaryForm_homogeneous 3 q⟩

/-- Polynomial identity transported BEFORE native section constructors. -/
private theorem originalMatrixRow_renamedCubicCut
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    (⟨rename finTwoEquiv (binaryForm 3 (A i)),
      (binaryForm_homogeneous 3 (A i)).rename_isHomogeneous⟩ : homogeneousSubmodule Bool K 3) =
    standardTwistedCubicLiteralLineLinearPolynomial (K := K) A i := by
  apply Subtype.ext
  exact congrArg (rename finTwoEquiv) (originalMatrixRow_binaryCubicCut (K := K) A i)

/-- SAME four rows of the original invertible ground matrix, carried by
the checked coefficient-to-GENUINE-native-H0 equivalence. -/
def groundMatrixNativeCubicHZeroBasis
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det) :
    Basis (Fin 4) K Hthree := by
  classical
  exact (basisOfPiSpaceOfLinearIndependent
    (Matrix.linearIndependent_rows_of_det_ne_zero (A := A) hA.ne_zero)).map
      (binaryCubicCoefficientsNativeHZeroLinearEquiv (K := K))

/-- The constructed basis elements are the EXACT original literal
parametrizing cubic sections, including both middle coordinates. -/
theorem groundMatrixNativeCubicHZeroBasis_apply
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A.det) (i : Fin 4) :
    groundMatrixNativeCubicHZeroBasis (K := K) A hA i =
    (N).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading L) 3
        (actualLineHomogeneousQuotientPiece K 3
          (standardTwistedCubicLiteralLineLinearPolynomial (K := K) A i))) := by
  simp only [groundMatrixNativeCubicHZeroBasis, Basis.map_apply,
    coe_basisOfPiSpaceOfLinearIndependent]
  exact (nativeBinaryCoefficients_literalSectionCut (K := K) (A i)).trans
    (congrArg (fun p : homogeneousSubmodule Bool K 3 =>
      (N).unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading L) 3
        (actualLineHomogeneousQuotientPiece K 3 p)))
      (originalMatrixRow_renamedCubicCut (K := K) A i))

/-- The SAME matrix selected by the EXISTING original ground
presentation determines the literal native cubic basis. -/
def GroundTwistedCubicPresentation.nativeCubicHZeroBasis
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) :
    Basis (Fin 4) K Hthree :=
  let A : GL (Fin 4) K := Classical.choose hB
  groundMatrixNativeCubicHZeroBasis (K := K) (A : Matrix (Fin 4) (Fin 4) K)
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A))

/-- No second cubic tuple: these are the original chosen ground images. -/
theorem GroundTwistedCubicPresentation.nativeCubicHZeroBasis_apply
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    hB.nativeCubicHZeroBasis i = hB.literalChosenNativeCubicSectionHom i := by
  let A : GL (Fin 4) K := Classical.choose hB
  exact groundMatrixNativeCubicHZeroBasis_apply (K := K) (A : Matrix (Fin 4) (Fin 4) K)
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)) i

/-- Native sheaf Iso gives its actual canonical K-linear H0 equivalence.
Both directions are the ORIGINAL whole morphism compositions; no inverse
basis, section image or H0-bijectivity certificate is supplied. -/
private def nativeWholeSectionIsoLinearEquivCut
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) {Q Q' : X.Modules} (e : Q ≅ Q') :
    SchemeModuleGlobalSectionsOver p Q ≃ₗ[K] SchemeModuleGlobalSectionsOver p Q' where
  toFun := schemeModuleGlobalSectionsMap p e.hom
  invFun := schemeModuleGlobalSectionsMap p e.inv
  left_inv s := by
    change (s ≫ e.hom) ≫ e.inv = s
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv s := by
    change (s ≫ e.inv) ≫ e.hom = s
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  map_add' s t := (schemeModuleGlobalSectionsMap p e.hom).map_add s t
  map_smul' c s := (schemeModuleGlobalSectionsMap p e.hom).map_smul c s

/-- GENUINE native H0 basis of the ORIGINAL ambient O(1) pullback under
the EXACT existing original ground parametrization. Its elements are
identified below with the ORIGINAL four pulled ambient coordinate maps. -/
def GroundTwistedCubicPresentation.nativeAmbientPulledCoordinateBasis
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) :
    Basis (Fin 4) K
      (SchemeModuleGlobalSectionsOver (toBase L)
        ((Scheme.Modules.pullback (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B)).obj
          (positiveSheafOfModules PS 1))) :=
  hB.nativeCubicHZeroBasis.map
    (nativeWholeSectionIsoLinearEquivCut (toBase L) hB.nativeAmbientPositiveOnePullbackIso).symm

/-- Complete-series assertion at whole-map level: every element of the
native pullback H0 basis is its SAME ORIGINAL pulled coordinate section. -/
theorem GroundTwistedCubicPresentation.nativeAmbientPulledCoordinateBasis_apply
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    hB.nativeAmbientPulledCoordinateBasis i =
    actualLineAmbientPulledCoordinateHom
      (hB.schemeIsoProjectiveLine.inv ≫ quotientProjMap B) i := by
  let E := nativeWholeSectionIsoLinearEquivCut (toBase L) hB.nativeAmbientPositiveOnePullbackIso
  have hi : hB.nativeAmbientPulledCoordinateBasis i = E.symm (hB.nativeCubicHZeroBasis i) :=
    Basis.map_apply _ _ i
  apply E.injective
  exact (congrArg E hi).trans ((E.apply_symm_apply _).trans
    ((hB.nativeCubicHZeroBasis_apply i).trans
      (hB.nativeAmbientPositiveOnePullbackIso_coordinate i).symm))

end PfaffianDescent.QuarticNet
