import PfaffianDescent.CorayAiNativeDenominatorSameGenericImageFactor
import PfaffianDescent.CorayOriginalGenericDifferentialDimensionAndSmoothImage

/-! The SAME actual native denominator-open representative maps into the
SAME whole image and admits a dense ORIGINAL surface open on which the
image point is smooth over ORIGINAL K. No smooth-open premise supplied.
SOURCE ONLY / UNCHECKED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal native denominator-open map into SAME C can be shrunk to
an actual dense ORIGINAL surface open whose points all map into the
constructed SAME image smooth locus. The exact native map and original
K structural square are retained, without replacing C or its map. -/
theorem cubicThroughPointBasis_nativeDenominatorOpen_exists_denseOriginalImageSmoothOpen001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let x : Fin m → R := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (b i)
    let B := Localization.Away (x a)
    let u : Spec (.of B) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
    let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
    ∃ f : Spec (.of B) ⟶ C,
      f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
        nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
      f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
        u ≫ hypersurfaceToBase p hp ∧
      ∃ W : TopologicalSpace.Opens (Spec (.of B)),
        W = f ⁻¹ᵁ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a ∧
        Dense (W : Set (Spec (.of B))) ∧
        ∃ V : TopologicalSpace.Opens S,
          (V : Set S) = u '' (W : Set (Spec (.of B))) ∧ Dense (V : Set S) ∧
          ∀ q ∈ W, f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let R := ChartRing I j
  let x : Fin m → R := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (b i)
  let B := Localization.Away (x a)
  let u : Spec (.of B) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
  let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
  obtain ⟨ha, hDominant, hGeneric, hKer, f, hFactor, hBase⟩ :=
    cubicThroughPointBasis_nativeDenominatorOpen_exists_sameGenericImageFactor001 p hp hp0 n y hpy j b a
  let G : R →+* S.functionField := @affineChartGenericEvaluation R (inferInstance : CommRing R)
    S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstance : Nonempty (chartι I j).opensRange)
  let ell : B →+* S.functionField := IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
  let tau : Spec S.functionField ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom ell)
  letI : IsClosedImmersion (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a) :=
    cubicThroughPointBasisEvaluationImageInclusion_isClosedImmersion p hp hp0 n y hpy j b a
  have hSame : tau ≫ f = cubicThroughPointBasisGenericPointToImage p hp hp0 n y hpy j b a := by
    apply (cancel_mono (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a)).mp
    rw [Category.assoc, hFactor, cubicThroughPointBasisGenericPointToImage_factorization]
    exact hGeneric
  let W : TopologicalSpace.Opens (Spec (.of B)) :=
    f ⁻¹ᵁ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a
  let q : Spec (.of B) := tau (genericPoint (Spec S.functionField))
  have hq : q ∈ W := by
    change f (tau (genericPoint (Spec S.functionField))) ∈
      cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a
    rw [← Scheme.Hom.comp_apply, hSame]
    exact cubicThroughPointBasisGenericPointToImage_mem_smoothOpen p hp hp0 n y hpy j b a
  letI : Nonempty (Spec (.of B)) := ⟨q⟩
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of R) (x a)
  letI : IsOpenImmersion (chartι I j) := isOpenImmersion_chartι I j
  letI : IsOpenImmersion u :=
    IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom (algebraMap R B))) (chartι I j)
  letI : IsIntegral (Spec (.of B)) := isIntegral_of_isOpenImmersion u
  have hW : (W : Set (Spec (.of B))).Nonempty := ⟨q, hq⟩
  have hWDense : Dense (W : Set (Spec (.of B))) := W.isOpen.dense hW
  let V : TopologicalSpace.Opens S :=
    ⟨u '' (W : Set (Spec (.of B))), u.isOpenEmbedding.isOpenMap _ W.isOpen⟩
  have hVDense : Dense (V : Set S) := V.isOpen.dense (hW.image u)
  exact ⟨f, hFactor, hBase, W, rfl, hWDense, V, rfl, hVDense, fun _ h => h⟩

end PfaffianDescent.Coray
end
