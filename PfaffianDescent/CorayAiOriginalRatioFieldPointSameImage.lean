import PfaffianDescent.CorayOriginalBasisRatioField
import PfaffianDescent.CorayBoundedOriginalEvaluationImage
import PfaffianDescent.CorayAiNativeGenericImageDominance

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The SAME existing original ratio field internally produces a dominant
field point of the SAME full original image C. Exact original generic-point
precomposition and ORIGINAL K square are retained. No image-field or
dominance/factor outcome is supplied. -/
theorem cubicThroughPointOriginalBasisRatioField_exists_dominant_sameImagePoint001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
    ∃ eta : Spec (.of E) ⟶ cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
      IsDominant eta ∧ IsSchemeTheoreticallyDominant eta ∧
      Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ eta =
        cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a ∧
      eta ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
  classical
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let E := cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a
  let xi : Fin m → F := fun i => cubicThroughPointBasisGenericCoordinates p hp n y hpy j b i
  have ha : xi a ≠ 0 := cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a
  have hRat (i : Fin m) : xi i / xi a ∈ E := by
    exact cubicThroughPointGeneric_normalized_mem_originalBasisRatioField p hp n y hpy j b a (b i)
  let xE : Fin m → E := fun i => ⟨xi i / xi a, hRat i⟩
  have haOne : xE a = 1 := by
    apply Subtype.ext
    exact div_self ha
  have haE : xE a ≠ 0 := by rw [haOne]; exact one_ne_zero
  let gE := projectiveEvaluationChartMap (algebraMap K E) xE a haE
  let Psi := projectiveEvaluationPoint (algebraMap K E) xE a haE
  let tau := Spec.map (CommRingCat.ofHom E.val.toRingHom)
  have hCoeff : E.val.toRingHom.comp (algebraMap K E) =
      schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) := by
    ext c
    exact E.val.commutes c
  have hChart : E.val.toRingHom.comp gE = cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a := by
    apply projectiveChartMap_ext a
    · rw [RingHom.comp_assoc, projectiveEvaluationChartMap_base, hCoeff]
      exact (projectiveEvaluationChartMap_base
        (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)) xi a ha).symm
    · intro i
      change E.val (projectiveEvaluationChartMap (algebraMap K E) xE a haE
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i)) =
          projectiveEvaluationChartMap
            (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)) xi a ha
            (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a i)
      rw [projectiveEvaluationChartMap_coordinate, projectiveEvaluationChartMap_coordinate, haOne, div_one]
      rfl
  have hGeneric : tau ≫ Psi = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a := by
    dsimp only [tau, Psi, projectiveEvaluationPoint, cubicThroughPointBasisGenericPoint]
    rw [← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a) hChart
  have hDominantKer := injective_fieldSpec_precomposition_ker_eq001 E.val.toRingHom
    Subtype.val_injective Psi
  have hKernel : (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker = Psi.ker := by
    rw [← hGeneric]
    exact hDominantKer.2
  let eta : Spec (.of E) ⟶ cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a :=
    Psi.toImage ≫ Scheme.IdealSheafData.inclusion (le_of_eq hKernel)
  have hFactor : eta ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a = Psi := by
    change ((Psi.toImage : Spec (.of E) ⟶ Psi.ker.subscheme) ≫
      (Scheme.IdealSheafData.inclusion (le_of_eq hKernel) : Psi.ker.subscheme ⟶
        (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker.subscheme)) ≫
      (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker.subschemeι = Psi
    calc
      _ = Psi.toImage ≫ (Scheme.IdealSheafData.inclusion (le_of_eq hKernel) ≫
          (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker.subschemeι) :=
        Category.assoc _ _ _
      _ = Psi.toImage ≫ Psi.ker.subschemeι :=
        congrArg (fun h => (Psi.toImage : Spec (.of E) ⟶ Psi.ker.subscheme) ≫ h)
          (Scheme.IdealSheafData.inclusion_subschemeι (le_of_eq hKernel))
      _ = Psi := Scheme.Hom.toImage_imageι Psi
  letI : IsClosedImmersion (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a) :=
    cubicThroughPointBasisEvaluationImageInclusion_isClosedImmersion p hp hp0 n y hpy j b a
  have hCompare : tau ≫ eta = cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a := by
    apply (cancel_mono (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a)).mp
    rw [Category.assoc, hFactor, hGeneric,
      cubicThroughPointBasisGenericPointToImage_factorization]
  letI : IsIntegral (cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a) :=
    cubicThroughPointBasisEvaluationImage_isIntegral p hp hp0 n y hpy j b a
  letI : IsDominant (tau ≫ eta) := by
    rw [hCompare]
    exact cubicThroughPointBasisGenericPointToImage_isDominant p hp hp0 n y hpy j b a
  letI : IsDominant eta := IsDominant.of_comp tau eta
  letI : IsSchemeTheoreticallyDominant eta := IsSchemeTheoreticallyDominant.of_isDominant eta
  refine ⟨eta, inferInstance, inferInstance, hCompare, ?_⟩
  change eta ≫ (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a ≫ _) = _
  rw [← Category.assoc, hFactor, projectiveEvaluationPoint_toBase]

end PfaffianDescent.Coray
