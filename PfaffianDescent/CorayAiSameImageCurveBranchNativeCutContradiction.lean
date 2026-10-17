import PfaffianDescent.CorayAiNativeDenominatorSameGenericImageFactor
import PfaffianDescent.CorayOriginalNativeHyperplaneWholeCurveRestrictionIso
import PfaffianDescent.CorayAiNativeHyperplanePullbackIncidence
import PfaffianDescent.CorayAiSameImageHyperplaneClosedPoints

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Pullback of the original denominator open is explicitly an open immersion. -/
private theorem wholeNativeCut_curvePullback_snd_isOpenImmersion005
    {U X C : Scheme.{u}} (i : U ⟶ X) (k : C ⟶ X) [IsOpenImmersion i] :
    IsOpenImmersion (pullback.snd i k) :=
  MorphismProperty.pullback_snd (P := @IsOpenImmersion.{u}) i k inferInstance

/-- On an integral scheme, a scheme map whose actual image points are all
closed is constant. The carrier and generic point are kept explicitly Scheme. -/
private theorem wholeNativeCut_integral_closedImages_equal004
    {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y)
    (hClosed : ∀ z : X, IsClosed ({g z} : Set Y)) (z₀ z₁ : X) : g z₀ = g z₁ := by
  have hEqual (z : X) : g z = g (genericPoint X) := by
    have hSpecializes : g (genericPoint X) ⤳ g z :=
      (genericPoint_specializes z).map g.continuous
    have hz := specializes_iff_mem_closure.mp hSpecializes
    rw [(hClosed (genericPoint X)).closure_eq] at hz
    exact Set.mem_singleton_iff.mp hz
  exact (hEqual z₀).trans (hEqual z₁).symm

/-- Two actual distinct native-cut images in the image-CURVE branch
construct a fresh original q whose WHOLE original intersection is nonintegral.
Curve dimension and the two native points remain honest construction inputs;
every comparison, factor, original-K map, and closed-image fact is derived. -/
theorem cubicThroughPointBasis_curveBranch_twoNativeCutImages_exists_nonintegralWholeMember001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) (hc : c ≠ 0)
    (hDim : ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
      Ring.DimensionLEOne
        ((cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a).presheaf.stalk z)) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let Phi := nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
    let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a))
    let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
    ∀ z₀ z₁ : (pullback v h : Scheme),
      Phi (pullback.fst v h z₀) ≠ Phi (pullback.fst v h z₁) →
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
        q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        Ideal.Quotient.mk I.toIdeal q = (∑ i, c i • b i).1.1 ∧
        ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
  let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
  let Phi := nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
  let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a))
  let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
  let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
  change ∀ z₀ z₁ : (pullback v h : Scheme),
    Phi (pullback.fst v h z₀) ≠ Phi (pullback.fst v h z₁) →
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
        q.eval₂ (algebraMap K L) y = 0 ∧ q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        Ideal.Quotient.mk I.toIdeal q = (∑ i, c i • b i).1.1 ∧
        ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))
  intro z₀ z₁ hDistinct
  obtain ⟨_hGa, _hDominant, _hGeneric, _hKernel, fC, hFactor, _hBase⟩ :=
    cubicThroughPointBasis_nativeDenominatorOpen_exists_sameGenericImageFactor001
      p hp hp0 n y hpy j b a
  obtain ⟨_hDenominator, q, hq, hy, hnot, hClass, E, _hE⟩ :=
    cubicThroughPointBasis_nativeHyperplanePullback_exists_sameWholeCurveRestrictionIso001
      p hp hp0 n y hpy j b a c hc
  let k := cubicSecondEquationCurveImmersion p q hp n hq
  let g : pullback v h ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) :=
    pullback.fst v h ≫ Phi
  have hClosed : ∀ z : (pullback v h : Scheme), IsClosed ({g z} : Set
      (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)))) := by
    intro z
    have hImage := congrArg (fun f => f (pullback.fst v h z)) hFactor
    change cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
      (fC (pullback.fst v h z)) = Phi (pullback.fst v h z) at hImage
    have hIncidence := nativeLocalizedProjectiveHyperplanePullback_images_mem_support001
      (chartBaseMap I j) x a c z
    have hIncidenceC : cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
        (fC (pullback.fst v h z)) ∈ basisProjectiveHyperplaneSupport c := by
      rw [hImage]
      exact hIncidence
    have h := (cubicThroughPointBasis_sameImage_hyperplaneCut_finite_closedPoints001
      p hp hp0 n y hpy j b a c hc hDim).2 _ hIncidenceC
    rw [hImage] at h
    exact h
  refine ⟨q, hq, hy, hnot, hClass, ?_⟩
  intro hWhole
  letI : IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := hWhole
  letI : IsOpenImmersion u := by dsimp only [u]; infer_instance
  letI : IsOpenImmersion (pullback.snd u k) :=
    wholeNativeCut_curvePullback_snd_isOpenImmersion005 u k
  let o : (pullback v h : Scheme) ⟶ scheme (projectiveIntersectionIdeal p q hp hq) :=
    E.hom ≫ pullback.snd u k
  letI : IsOpenImmersion o := by dsimp only [o]; infer_instance
  letI : Nonempty (pullback v h : Scheme) := ⟨z₀⟩
  letI : IsIntegral (pullback v h : Scheme) := isIntegral_of_isOpenImmersion o
  exact hDistinct (wholeNativeCut_integral_closedImages_equal004 g hClosed z₀ z₁)

end PfaffianDescent.Coray
