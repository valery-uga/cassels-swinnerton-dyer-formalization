import PfaffianDescent.CorayAiNativeDenominatorSameGenericImageFactor
import PfaffianDescent.CorayOriginalNativeHyperplaneWholeCurveRestrictionIso
import PfaffianDescent.CorayAiNativeHyperplanePullbackIncidence

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Inverse projection transport on abstract schemes bounds the comparison
before substituting the original native pullbacks. -/
private theorem wholeNativeCut_inverse_projection004
    {X Y Z : Scheme.{u}} (E : X ≅ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    (h : E.hom ≫ f = g) : E.inv ≫ g = f := by
  calc
    E.inv ≫ g = E.inv ≫ (E.hom ≫ f) := congrArg (E.inv ≫ ·) h.symm
    _ = f := by simp only [Iso.inv_hom_id_assoc]

/-- Pullback of the original denominator open is explicitly an open immersion. -/
private theorem wholeNativeCut_pullback_snd_isOpenImmersion004
    {U X C : Scheme.{u}} (i : U ⟶ X) (k : C ⟶ X) [IsOpenImmersion i] :
    IsOpenImmersion (pullback.snd i k) :=
  MorphismProperty.pullback_snd (P := @IsOpenImmersion.{u}) i k inferInstance

/-- Both exact image and original-base squares transport across the actual
whole-cut isomorphism. All objects stay abstract in this bounded proof cut. -/
private theorem wholeNativeCut_transport_existingImage_map004
    {U A H X Q C T Z : Scheme.{u}}
    (v : U ⟶ A) (h : H ⟶ A) (i : U ⟶ X) (k : Q ⟶ X)
    (E : pullback v h ≅ pullback i k)
    (fC : U ⟶ C) (inc : C ⟶ T) (Phi : U ⟶ T)
    (base : C ⟶ Z) (pi : X ⟶ Z)
    (hE : E.hom ≫ pullback.fst i k = pullback.fst v h)
    (hFactor : fC ≫ inc = Phi) (hBase : fC ≫ base = i ≫ pi) :
    ∃ f : pullback i k ⟶ C,
      f ≫ inc = E.inv ≫ pullback.fst v h ≫ Phi ∧
      f ≫ base = pullback.snd i k ≫ k ≫ pi := by
  let f : pullback i k ⟶ C := E.inv ≫ pullback.fst v h ≫ fC
  have hLeft : E.inv ≫ pullback.fst v h = pullback.fst i k :=
    wholeNativeCut_inverse_projection004 E (pullback.fst i k) (pullback.fst v h) hE
  have hSquare : (E.inv ≫ pullback.fst v h) ≫ i = pullback.snd i k ≫ k := by
    rw [hLeft]
    exact pullback.condition
  refine ⟨f, ?_, ?_⟩
  · simp only [f, Category.assoc, hFactor]
  · calc
      f ≫ base = (E.inv ≫ pullback.fst v h) ≫ (i ≫ pi) := by
        simp only [f, Category.assoc, hBase]
      _ = ((E.inv ≫ pullback.fst v h) ≫ i) ≫ pi := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ pi) hSquare

/-- The native cut is an actual open of the WHOLE original q-curve and
maps to the SAME original generic image C. Its ORIGINAL K square and ALL
hyperplane incidences are derived; factorization and comparison are constructed
by their actual producers, never input as desired outcome hypotheses. -/
theorem cubicThroughPointBasis_wholeNativeCut_exists_sameImageMap001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) (hc : c ≠ 0) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a))
    let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
    let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk I.toIdeal q = (∑ i, c i • b i).1.1 ∧
      let k := cubicSecondEquationCurveImmersion p q hp n hq
      ∃ (E : pullback v h ≅ pullback u k)
        (f : pullback u k ⟶ cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a),
        IsOpenImmersion (pullback.snd u k) ∧
        E.hom ≫ pullback.fst u k = pullback.fst v h ∧
        f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
          E.inv ≫ pullback.fst v h ≫ nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
        f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          pullback.snd u k ≫ k ≫ hypersurfaceToBase p hp ∧
        ∀ z : (pullback u k : Scheme),
          cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a (f z) ∈
            basisProjectiveHyperplaneSupport c := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
  let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
  let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a))
  let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
  let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
  obtain ⟨_hGa, _hDominant, _hGeneric, _hKernel, fC, hFactor, hBase⟩ :=
    cubicThroughPointBasis_nativeDenominatorOpen_exists_sameGenericImageFactor001
      p hp hp0 n y hpy j b a
  obtain ⟨_hDenominator, q, hq, hy, hnot, hClass, E, hE⟩ :=
    cubicThroughPointBasis_nativeHyperplanePullback_exists_sameWholeCurveRestrictionIso001
      p hp hp0 n y hpy j b a c hc
  let k := cubicSecondEquationCurveImmersion p q hp n hq
  obtain ⟨f, hAmbient, hGround⟩ :=
    wholeNativeCut_transport_existingImage_map004 v h u k E fC
      (cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a)
      (nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a)
      (cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a)
      (hypersurfaceToBase p hp) hE hFactor hBase
  letI : IsOpenImmersion u := by dsimp only [u]; infer_instance
  have hOpen : IsOpenImmersion (pullback.snd u k) :=
    wholeNativeCut_pullback_snd_isOpenImmersion004 u k
  refine ⟨q, hq, hy, hnot, hClass, E, f, hOpen, hE, hAmbient, hGround, ?_⟩
  intro z
  have hImage := congrArg (fun g => g z) hAmbient
  change cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a (f z) =
    nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
      (pullback.fst v h (E.inv z)) at hImage
  rw [hImage]
  exact nativeLocalizedProjectiveHyperplanePullback_images_mem_support001
    (chartBaseMap I j) x a c (E.inv z)

end PfaffianDescent.Coray
