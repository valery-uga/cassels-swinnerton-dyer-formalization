import PfaffianDescent.NativeNormalizedPullbackSectionMap
import PfaffianDescent.TwistedCubicNativeGlobalCoordinateImages
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.ProjectiveLineLiteralHomogeneousHZeroLinear
import PfaffianDescent.QuarticTwistedCubicSmooth

/-! SOURCE ONLY. Extend the SAME four native images to ground linear
coordinates using actual canonical K-linear maps, not an image certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist ProjectiveLineNative
open BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "v" => standardProjectiveLineToTwistedCubic (K := K)
local notation "T" => positiveSheafOfModules (grading I) 1
local notation "N" => positiveSheafOfModules (grading L) 3
local notation "M" => CategoryTheory.Functor.obj (Scheme.Modules.pullback v) T

private noncomputable instance nativeLinearImageHZeroAddCommGroup
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    AddCommGroup (SchemeModuleGlobalSectionsOver p Q) :=
  instAddCommGroupSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

private noncomputable instance nativeLinearImageHZeroModule
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (Q : X.Modules) :
    Module K (SchemeModuleGlobalSectionsOver p Q) :=
  instModuleSchemeModuleGlobalSectionsOver (K := K) (X := X) p Q

private instance standardParametrizationOpenImmersion : IsOpenImmersion v := by
  haveI : IsIso v := by
    change IsIso (standardTwistedCubicProjectiveLineProjIso (K := K)).inv
    infer_instance
  infer_instance

/-- Install the original canonical unit comparison witness explicitly for
this concrete parametrization; all original inverse-map headers remain exact. -/
local instance standardParametrizationUnitComparisonIsIso :
    IsIso (pullbackUnitComparison v) := isIso_pullbackUnitComparison v

/-- The SAME original parametrization respects the literal structure map. -/
theorem standardTwistedCubicNativeParametrization_toBase : v ≫ toBase I = toBase L := by
  let e := standardTwistedCubicProjectiveLineProjIso (K := K)
  change e.inv ≫ toBase I = projectiveLineProjToBase K
  rw [← standardTwistedCubicProjectiveLineProjIso_hom_toBase,
    Iso.inv_hom_id_assoc]

private def originalPolynomialDegreeOneQuotientLinearMap : PS 1 →ₗ[K] grading I 1 :=
  ((Ideal.Quotient.mkₐ K (I).toIdeal).toLinearMap.comp (PS 1).subtype).codRestrict _
    (fun p => (quotientGradedRingHom I).2 p.property)

private theorem positiveHomogeneousGlobalSectionLinearMap_unitHom
    {σ : Type} [Finite σ] (J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (m : ℕ) (p : grading J m) :
    positiveHomogeneousGlobalSectionLinearMap J m p =
      (positiveSheafOfModules (grading J) m).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading J) m p) := by
  let Q := positiveSheafOfModules (grading J) m
  change Q.unitHomEquiv.symm
    ((schemeModuleSectionsEquivTop Q).symm ((schemeModuleSectionsEquivTop Q)
      (positiveGlobalSectionOfHomogeneous (grading J) m p))) = _
  rw [Equiv.symm_apply_apply]

/-- Actual linear map from original linear polynomials to the whole native
O3 sections through the SAME pullback and SAME global comparison Iso. -/
def standardTwistedCubicNativeLinearImageMap :
    PS 1 →ₗ[K] SchemeModuleGlobalSectionsOver (toBase L) N :=
  (schemeModuleGlobalSectionsMap (toBase L)
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom).comp
    (((schemeModuleGlobalSectionsBaseEqLinearEquiv (v ≫ toBase I) (toBase L)
      (standardTwistedCubicNativeParametrization_toBase (K := K)) M).toLinearMap.comp
        (nativeNormalizedPullbackGlobalSectionLinearMap v (toBase I) T)).comp
      ((positiveHomogeneousGlobalSectionLinearMap I 1).comp
        (originalPolynomialDegreeOneQuotientLinearMap (K := K))))

private def standardTwistedCubicLiteralDegreeOnePolynomialMap :
    PS 1 →ₗ[K] homogeneousSubmodule Bool K 3 :=
  ((((rename finTwoEquiv).comp (standardTwistedCubicParam K)).toLinearMap.comp
    (PS 1).subtype).codRestrict _ (fun p => by
      have h : (standardTwistedCubicParam K (p : MvPolynomial (Fin 4) K)).IsHomogeneous 3 := by
        simpa only [Nat.mul_one] using standardTwistedCubicParam_homogeneous p.property
      exact h.rename_isHomogeneous))

/-- The literal cubic polynomial of an original ground linear coordinate,
under the SAME standard polynomial parametrization and canonical renaming. -/
def standardTwistedCubicLiteralLineLinearPolynomial
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) : homogeneousSubmodule Bool K 3 :=
  ⟨rename finTwoEquiv (standardTwistedCubicParam K (linearCoordinate A i)), by
    have h : (standardTwistedCubicParam K (linearCoordinate A i)).IsHomogeneous 3 := by
      simpa only [Nat.mul_one] using
        standardTwistedCubicParam_homogeneous (linearCoordinate_homogeneous A i)
    exact h.rename_isHomogeneous⟩

/-- Genuine literal polynomial-section map; the ORIGINAL native H0
equivalence supplies its K-linearity, with its original toBase action. -/
def standardTwistedCubicLiteralLinearImageMap :
    PS 1 →ₗ[K] SchemeModuleGlobalSectionsOver (toBase L) N :=
  (actualLineLiteralHomogeneousHZeroLinearEquiv K 3).toLinearMap.comp
    (standardTwistedCubicLiteralDegreeOnePolynomialMap (K := K))

private theorem standardLiteralLinearImageMap_coordinate (k : Fin 4) :
    standardTwistedCubicLiteralLinearImageMap (K := K) ⟨X k, isHomogeneous_X K k⟩ =
    standardTwistedCubicLiteralLineSectionHom (K := K) k := by
  exact actualLineLiteralHomogeneousHZeroLinearEquiv_apply K 3
    (standardTwistedCubicLiteralDegreeOnePolynomialMap (K := K) ⟨X k, isHomogeneous_X K k⟩)

/-- Evaluate the SAME actual normalized/global/base-transport composition
while schemes, modules, the incoming linear map and section remain abstract. -/
private theorem nativeLinearImageComposition_applyCut
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (p : Y ⟶ Spec (.of K)) (p' : X ⟶ Spec (.of K)) (hp : f ≫ p = p')
    (Q : Y.Modules) (Q' : X.Modules) (e : (Scheme.Modules.pullback f).obj Q ⟶ Q')
    {V : Type u} [AddCommGroup V] [Module K V]
    (l : V →ₗ[K] SchemeModuleGlobalSectionsOver p Q) (x : V) :
    ((schemeModuleGlobalSectionsMap p' e).comp
      (((schemeModuleGlobalSectionsBaseEqLinearEquiv (f ≫ p) p' hp
        ((Scheme.Modules.pullback f).obj Q)).toLinearMap.comp
          (nativeNormalizedPullbackGlobalSectionLinearMap f p Q)).comp l)) x =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
      (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map (l x) ≫ e := by
  change (CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
    (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map (l x)) ≫ e = _
  exact Category.assoc _ _ _

private theorem originalDegreeOneQuotient_coordinateCut (k : Fin 4) :
    originalPolynomialDegreeOneQuotientLinearMap (K := K) ⟨X k, isHomogeneous_X K k⟩ =
      (⟨coordinate I k, coordinate_mem I k⟩ : grading I 1) := rfl

/-- Convert only the polynomial-linear-map/actual section constructor. -/
private theorem originalDegreeOneSection_coordinateCut (k : Fin 4) :
    positiveHomogeneousGlobalSectionLinearMap I 1
      (originalPolynomialDegreeOneQuotientLinearMap (K := K) ⟨X k, isHomogeneous_X K k⟩) =
    standardTwistedCubicPositiveOneCoordinateHom (K := K) k := by
  exact (congrArg (positiveHomogeneousGlobalSectionLinearMap I 1)
    (originalDegreeOneQuotient_coordinateCut (K := K) k)).trans
      (positiveHomogeneousGlobalSectionLinearMap_unitHom I 1
        ⟨coordinate I k, coordinate_mem I k⟩)

/-- Concrete specialization evaluates the pipeline without rewriting its
large composed linear-map constructor or an original positive sheaf. -/
private theorem standardNativeLinearImageMap_applyCut (p : PS 1) :
    standardTwistedCubicNativeLinearImageMap (K := K) p =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison v) (pullbackUnitComparison v) ≫
      (Scheme.Modules.pullback v).map
        (positiveHomogeneousGlobalSectionLinearMap I 1
          (originalPolynomialDegreeOneQuotientLinearMap (K := K) p)) ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom := by
  exact nativeLinearImageComposition_applyCut v (toBase I) (toBase L)
    (standardTwistedCubicNativeParametrization_toBase (K := K)) T N
    (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom
    ((positiveHomogeneousGlobalSectionLinearMap I 1).comp
      (originalPolynomialDegreeOneQuotientLinearMap (K := K))) p

/-- Whole-section evaluation is transported independently of literal H0
or the matrix-coordinate polynomial constructor. -/
private theorem standardNativeLinearImageMap_hom_applyCut (p : PS 1) :
    standardTwistedCubicNativeLinearImageMap (K := K) p =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison v) (pullbackUnitComparison v) ≫
      (Scheme.Modules.pullback v).map
        ((positiveSheafOfModules (grading I) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading I) 1
            (originalPolynomialDegreeOneQuotientLinearMap (K := K) p))) ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom := by
  exact (standardNativeLinearImageMap_applyCut (K := K) p).trans
    (congrArg (fun s =>
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison v) (pullbackUnitComparison v) ≫
        (Scheme.Modules.pullback v).map s ≫
        (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom)
      (positiveHomogeneousGlobalSectionLinearMap_unitHom I 1
        (originalPolynomialDegreeOneQuotientLinearMap (K := K) p)))

/-- Expose only the original pulled-coordinate normalization and its
association with the SAME global comparison hom. -/
private theorem originalPulledCoordinate_comp_eq_normalizedCut (k : Fin 4) :
    standardTwistedCubicPulledCoordinateHom (K := K) k ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison v) (pullbackUnitComparison v) ≫
      (Scheme.Modules.pullback v).map (standardTwistedCubicPositiveOneCoordinateHom (K := K) k) ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom := by
  change (CategoryTheory.inv («I» := isIso_pullbackUnitComparison v)
    (pullbackUnitComparison v) ≫
      (Scheme.Modules.pullback v).map (standardTwistedCubicPositiveOneCoordinateHom (K := K) k)) ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom = _
  exact Category.assoc _ _ _

private theorem standardNativeLinearImageMap_coordinate (k : Fin 4) :
    standardTwistedCubicNativeLinearImageMap (K := K) ⟨X k, isHomogeneous_X K k⟩ =
    standardTwistedCubicLiteralLinearImageMap (K := K) ⟨X k, isHomogeneous_X K k⟩ := by
  exact (standardNativeLinearImageMap_applyCut (K := K) ⟨X k, isHomogeneous_X K k⟩).trans
    ((congrArg (fun s =>
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison v) (pullbackUnitComparison v) ≫
        (Scheme.Modules.pullback v).map s ≫
        (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom)
      (originalDegreeOneSection_coordinateCut (K := K) k)).trans
      (((originalPulledCoordinate_comp_eq_normalizedCut (K := K) k).symm.trans
        (standardTwistedCubicNativePositiveOnePullbackIso_coordinate (K := K) k)).trans
        (standardLiteralLinearImageMap_coordinate (K := K) k).symm))

/-- Every original ground linear coordinate has the literal parametrizing
cubic image, derived from all four whole-coordinate identities and linearity. -/
theorem standardTwistedCubicNativePositiveOnePullbackIso_linearCoordinate
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    standardTwistedCubicNativeLinearImageMap (K := K)
      ⟨linearCoordinate A i, linearCoordinate_homogeneous A i⟩ =
    standardTwistedCubicLiteralLinearImageMap (K := K)
      ⟨linearCoordinate A i, linearCoordinate_homogeneous A i⟩ := by
  classical
  have hp : (⟨linearCoordinate A i, linearCoordinate_homogeneous A i⟩ : PS 1) =
      ∑ j : Fin 4, A i j • (⟨X j, isHomogeneous_X K j⟩ : PS 1) := by
    apply Subtype.ext
    simp [linearCoordinate, Matrix.mulVec, dotProduct, smul_eq_C_mul]
  rw [hp]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg (A i j • ·)
    (standardNativeLinearImageMap_coordinate (K := K) j))

/-- Whole native-map formulation of the ground linear-coordinate image;
the right-hand side is its literal original polynomial-section constructor. -/
theorem standardTwistedCubicNativePositiveOnePullbackIso_linearCoordinate_hom
    (A : Matrix (Fin 4) (Fin 4) K) (i : Fin 4) :
    inv (pullbackUnitComparison v) ≫ (Scheme.Modules.pullback v).map
      ((positiveSheafOfModules (grading I) 1).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 1
          ⟨Ideal.Quotient.mk (I).toIdeal (linearCoordinate A i),
            (quotientGradedRingHom I).2 (linearCoordinate_homogeneous A i)⟩)) ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom =
    (positiveSheafOfModules (grading L) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading L) 3
        (actualLineHomogeneousQuotientPiece K 3
          (standardTwistedCubicLiteralLineLinearPolynomial (K := K) A i))) := by
  exact (standardNativeLinearImageMap_hom_applyCut (K := K)
      ⟨linearCoordinate A i, linearCoordinate_homogeneous A i⟩).symm.trans
    ((standardTwistedCubicNativePositiveOnePullbackIso_linearCoordinate (K := K) A i).trans
      (actualLineLiteralHomogeneousHZeroLinearEquiv_apply K 3
        (standardTwistedCubicLiteralDegreeOnePolynomialMap (K := K)
          ⟨linearCoordinate A i, linearCoordinate_homogeneous A i⟩)))

end PfaffianDescent.QuarticNet
