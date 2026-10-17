import PfaffianDescent.CorayAiNativeGenericImageDominance
import PfaffianDescent.CorayAiNativeFieldChartComparison
import PfaffianDescent.CorayBoundedOriginalEvaluationImage

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native denominator-open map factors through the SAME existing
original generic image C, with its exact original-K structural square.
The actual kernel equality is derived from schematic dominance, preserving
the full scheme structures instead of only their reduced supports. -/
theorem cubicThroughPointBasis_nativeDenominatorOpen_exists_sameGenericImageFactor001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    let G : R →+* (hypersurface p hp).functionField :=
      @affineChartGenericEvaluation R (inferInstance : CommRing R)
        (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
        (chartι I j) (isOpenImmersion_chartι I j)
        (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
    ∃ hGa : G (x a) ≠ 0,
      let ell : Localization.Away (x a) →+* S.functionField :=
        IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr hGa)
      let tau : Spec S.functionField ⟶ Spec (.of (Localization.Away (x a))) :=
        Spec.map (CommRingCat.ofHom ell)
      let Phi := nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
      let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
      IsSchemeTheoreticallyDominant tau ∧
      tau ≫ Phi = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a ∧
      Phi.ker = (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker ∧
      ∃ f : Spec (.of (Localization.Away (x a))) ⟶
          cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
        f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a = Phi ∧
        f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          u ≫ hypersurfaceToBase p hp := by
  classical
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let R := ChartRing I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let G : R →+* (hypersurface p hp).functionField :=
      @affineChartGenericEvaluation R (inferInstance : CommRing R)
        (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
        (chartι I j) (isOpenImmersion_chartι I j)
        (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  have hG : Function.Injective G :=
    @affineChartGenericEvaluation_injective R (inferInstance : CommRing R)
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstance : Nonempty (chartι (equationIdeal p hp) j).opensRange)
  have he : Function.Injective e := cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j
  have hGa : G (x a) ≠ 0 := by
    intro hZero
    apply b.ne_zero a
    apply he
    rw [map_zero]
    apply hG
    exact hZero.trans (map_zero G).symm
  refine ⟨hGa, ?_⟩
  let ell : Localization.Away (x a) →+* S.functionField :=
    IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr hGa)
  let tau : Spec S.functionField ⟶ Spec (.of (Localization.Away (x a))) :=
    Spec.map (CommRingCat.ofHom ell)
  let Phi := nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
  let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
  have hEll : Function.Injective ell := localizationAway_fieldLift_injective_of_injective001 G hG (x a) hGa
  have hDominant := injective_fieldSpec_precomposition_ker_eq001 ell hEll Phi
  have hCoeff : G.comp (chartBaseMap I j) = schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp) :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  have hCoordinates : (fun i => G (x i)) = cubicThroughPointBasisGenericCoordinates p hp n y hpy j b := rfl
  have hChart := nativeLocalizedProjectiveChartMap_fieldLift_eq_genericChartMap001
    (chartBaseMap I j) x a G hGa
  have hChartNative : ell.comp (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a) =
      cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a := by
    rw [hCoeff] at hChart
    exact hChart
  have hGeneric : tau ≫ Phi = cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a := by
    dsimp only [tau, Phi, nativeLocalizedProjectiveChartPoint, cubicThroughPointBasisGenericPoint]
    rw [← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a) hChartNative
  have hKer : (cubicThroughPointBasisGenericPoint p hp hp0 n y hpy j b a).ker = Phi.ker := by
    rw [← hGeneric]
    exact hDominant.2
  let f : Spec (.of (Localization.Away (x a))) ⟶
      cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a :=
    Phi.toImage ≫ Scheme.IdealSheafData.inclusion (le_of_eq hKer)
  have hFactor : f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a = Phi := by
    dsimp only [f, cubicThroughPointBasisEvaluationImageInclusion]
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]
  refine ⟨hDominant.1, hGeneric, hKer.symm, f, hFactor, ?_⟩
  change f ≫ (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a ≫ _) = _
  rw [← Category.assoc, hFactor, nativeLocalizedProjectiveChartPoint_toBase001]
  dsimp only [u]
  change Spec.map (CommRingCat.ofHom
      ((algebraMap R (Localization.Away (x a))).comp (chartBaseMap I j))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫
      (chartι I j ≫ toBase I)
  rw [chartι_toBase, ← Spec.map_comp]
  rfl

end PfaffianDescent.Coray
