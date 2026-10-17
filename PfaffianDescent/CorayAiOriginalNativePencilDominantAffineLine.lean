import PfaffianDescent.CorayOriginalBasisTranscendentalRatio
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-! SOURCE ONLY. The literal pencil ratio on a native denominator open
produces a dominant finite-type morphism to the original affine line. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual affine-line coordinate map, with the unchanged coefficient
hom followed by native localization. x₀ is the denominator, x₁ numerator. -/
def nativeLocalizedPencilCoordinateMap001
    {K R : Type u} [Field K] [CommRing R]
    (f : K →+* R) (x₀ x₁ : R) :
    MvPolynomial (ULift.{u} (Fin 1)) K →+* Localization.Away x₀ :=
  (Polynomial.eval₂RingHom ((algebraMap R (Localization.Away x₀)).comp f)
    (algebraMap R (Localization.Away x₀) x₁ * IsLocalization.Away.invSelf x₀)).comp
      (MvPolynomial.uniqueAlgEquiv K (ULift.{u} (Fin 1))).toRingHom

/-- Literal native scheme morphism to A¹_K; the standard Spec isomorphism
only identifies its polynomial coordinate ring with actual affine space. -/
def nativeLocalizedPencilAffineLineMap001
    {K R : Type u} [Field K] [CommRing R]
    (f : K →+* R) (x₀ x₁ : R) :
    Spec (.of (Localization.Away x₀)) ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) :=
  Spec.map (CommRingCat.ofHom (nativeLocalizedPencilCoordinateMap001 f x₀ x₁)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv

private theorem nativeLocalizedPencilCoordinateMap_injective001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (f : K →+* R) (g : R →+* F)
    (hCoeff : g.comp f = algebraMap K F) (x₀ x₁ : R)
    (hDenom : g x₀ ≠ 0) (hRatio : Transcendental K (g x₁ / g x₀)) :
    Function.Injective (nativeLocalizedPencilCoordinateMap001 f x₀ x₁) := by
  let B := Localization.Away x₀
  let l : R →+* B := algebraMap R B
  let t : K →+* B := l.comp f
  let z : B := l x₁ * IsLocalization.Away.invSelf x₀
  let G : B →+* F := IsLocalization.Away.lift x₀ (isUnit_iff_ne_zero.mpr hDenom)
  have hInverse : G (IsLocalization.Away.invSelf x₀) = (g x₀)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hDenom).mp
    have h := congrArg G (IsLocalization.Away.mul_invSelf (S := B) x₀)
    rw [map_mul, map_one, IsLocalization.Away.lift_eq] at h
    simpa only [mul_comm] using h
  have hImage : G z = g x₁ / g x₀ := by
    change G (l x₁ * IsLocalization.Away.invSelf x₀) = _
    rw [map_mul, IsLocalization.Away.lift_eq, hInverse, div_eq_mul_inv]
  let phi : Polynomial K →+* B := Polynomial.eval₂RingHom t z
  have hComposition : G.comp phi = (Polynomial.aeval (g x₁ / g x₀)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      change G (Polynomial.eval₂ t z (Polynomial.C c)) =
        Polynomial.aeval (g x₁ / g x₀) (Polynomial.C c)
      rw [Polynomial.eval₂_C, Polynomial.aeval_C]
      change G (l (f c)) = algebraMap K F c
      rw [IsLocalization.Away.lift_eq]
      exact RingHom.congr_fun hCoeff c
    · change G (Polynomial.eval₂ t z Polynomial.X) =
        Polynomial.aeval (g x₁ / g x₀) Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.aeval_X]
      exact hImage
  have hPoly : Function.Injective phi := by
    intro a b hab
    apply (transcendental_iff_injective.mp hRatio)
    have h := congrArg G hab
    change (G.comp phi) a = (G.comp phi) b at h
    rw [hComposition] at h
    exact h
  exact hPoly.comp (MvPolynomial.uniqueAlgEquiv K (ULift.{u} (Fin 1))).injective

/-- Transcendence of the actual generic ratio forces dominance of the
literal native map. Finite type and quasi-compactness are derived from
the finite-type coefficient chart and its native localization. -/
theorem nativeLocalizedPencilAffineLine_dominant_finiteType001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (f : K →+* R) (hf : f.FiniteType) (g : R →+* F)
    (hCoeff : g.comp f = algebraMap K F) (x₀ x₁ : R)
    (hDenom : g x₀ ≠ 0) (hRatio : Transcendental K (g x₁ / g x₀)) :
    IsDominant (nativeLocalizedPencilAffineLineMap001 f x₀ x₁) ∧
    LocallyOfFiniteType (nativeLocalizedPencilAffineLineMap001 f x₀ x₁) ∧
    QuasiCompact (nativeLocalizedPencilAffineLineMap001 f x₀ x₁) ∧
    nativeLocalizedPencilAffineLineMap001 f x₀ x₁ ≫
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) =
        Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away x₀)).comp f)) := by
  let B := Localization.Away x₀
  let l : R →+* B := algebraMap R B
  let t : K →+* B := l.comp f
  let phi := nativeLocalizedPencilCoordinateMap001 f x₀ x₁
  have hPhiInjective : Function.Injective phi :=
    nativeLocalizedPencilCoordinateMap_injective001 f g hCoeff x₀ x₁ hDenom hRatio
  have hPhiCoeff : phi.comp (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin 1)) K) = t := by
    ext c
    change Polynomial.eval₂ t (l x₁ * IsLocalization.Away.invSelf x₀)
      ((MvPolynomial.uniqueAlgEquiv K (ULift.{u} (Fin 1))) (MvPolynomial.C c)) = t c
    rw [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_C, Polynomial.eval₂_C]
  have hLocFinite : l.FiniteType := by
    apply RingHom.finiteType_algebraMap.mpr
    exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers x₀) B
  have hCoeffFinite : t.FiniteType := hLocFinite.comp hf
  have hPhiFinite : phi.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType
      (f := (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin 1)) K))
    rw [hPhiCoeff]
    exact hCoeffFinite
  let q := Spec.map (CommRingCat.ofHom phi)
  letI : IsDominant q := by
    constructor
    change DenseRange (PrimeSpectrum.comap phi)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical phi).mpr
    rw [(RingHom.injective_iff_ker_eq_bot phi).mp hPhiInjective]
    exact bot_le
  letI : LocallyOfFiniteType q :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hPhiFinite
  letI : QuasiCompact q := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · change IsDominant (q ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv)
    infer_instance
  · change LocallyOfFiniteType (q ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv)
    infer_instance
  · change QuasiCompact (q ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv)
    infer_instance
  change (q ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (phi.comp MvPolynomial.C)) = _
  rw [hPhiCoeff]

private theorem nativePencil_exactFamily_linearIndependent001
    {K V B F : Type u} [Field K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid B] [Module K B]
    [AddCommMonoid F] [Module K F]
    (e : V →ₗ[K] B) (he : Function.Injective e) (E : B ≃ₗ[K] F)
    (phi : V → F) (hphi : ∀ t : V, E (e t) = phi t)
    (s : Fin 2 → V) (hli : LinearIndependent K s) :
    LinearIndependent K (fun i => phi (s i)) := by
  let native : V →ₗ[K] F := E.toLinearMap.comp e
  have hNative : Function.Injective native := E.injective.comp he
  have hliNative : LinearIndependent K (native ∘ s) :=
    hli.map_injOn native hNative.injOn
  have hFamily : native ∘ s = (fun i => phi (s i)) :=
    funext (fun i => hphi (s i))
  exact hFamily ▸ hliNative

private theorem originalIndependentPencil_generic_ratio001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let v := fun i => (show (hypersurface p hp).functionField from
      cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s i))
    (∀ i, v i ≠ 0) ∧ Transcendental K (v 1 / v 0) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let V := cubicThroughCoordinateSections p hp n y hpy
  let B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)
  let F := (hypersurface p hp).functionField
  let e : V →ₗ[K] B := cubicThroughPointGenericLinearEvaluation p hp n y hpy j
  have he : Function.Injective e :=
    cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0
  let E : B ≃ₗ[K] F := schemeFunctionFieldOriginalRingLinearEquiv (hypersurfaceToBase p hp)
  let phi : V → F := fun t => (show F from e t)
  let v : Fin 2 → F := fun i => phi (s i)
  have hliNative : LinearIndependent K v :=
    nativePencil_exactFamily_linearIndependent001 (K := K) (V := V) (B := B) (F := F)
      e he E phi (fun _ => rfl) s hli
  refine ⟨fun i => hliNative.ne_zero i, ?_⟩
  intro hAlg
  have hGround := cubicOriginalFunctionField_isAlgebraic_mem_ground p hp hp0 j
    (v 1 / v 0) hAlg
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hGround
  have hval : v 1 = algebraMap K (hypersurface p hp).functionField c * v 0 :=
    (div_eq_iff (hliNative.ne_zero 0)).mp hc.symm
  have hsmul : (1 : K) • v 1 = c • v 0 := by
    simpa only [one_smul, Algebra.smul_def, map_one, one_mul] using hval
  exact (by decide : (1 : Fin 2) ≠ 0)
    (hliNative.eq_of_smul_apply_eq_smul_apply 1 c 1 0 one_ne_zero hsmul)

/-- The SAME actual independent original through-P sections construct a
native denominator-open map to A¹_K which is dominant, finite type and
quasi-compact. The source is an actual integral OPEN of the original cubic
and the exact original structural map is retained. No dominance or ratio
hypothesis is supplied; the cubic constant-field result derives it. -/
theorem originalIndependentPencil_native_denominatorOpen_dominant_affineLine001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s) :
    let x := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (s i)
    let f := nativeLocalizedPencilAffineLineMap001 (chartBaseMap (equationIdeal p hp) j) (x 0) (x 1)
    let i := Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing (equationIdeal p hp) j) (Localization.Away (x 0)))) ≫
        chartι (equationIdeal p hp) j
    IsDominant f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      IsOpenImmersion i ∧ IsIntegral (Spec (.of (Localization.Away (x 0)))) ∧
      f ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) =
        i ≫ hypersurfaceToBase p hp := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : IsOpenImmersion (chartι (equationIdeal p hp) j) :=
    isOpenImmersion_chartι (equationIdeal p hp) j
  let R := ChartRing (equationIdeal p hp) j
  let x := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (s i)
  let B := Localization.Away (x 0)
  let g : R →+* (hypersurface p hp).functionField :=
    affineChartGenericEvaluation (chartι (equationIdeal p hp) j)
  have hCoeff : g.comp (chartBaseMap (equationIdeal p hp) j) =
      algebraMap K (hypersurface p hp).functionField :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  obtain ⟨hValues, hRatio⟩ := originalIndependentPencil_generic_ratio001 p hp hp0 n y hpy j s hli
  have hDenom : g (x 0) ≠ 0 := hValues 0
  have hTrans : Transcendental K (g (x 1) / g (x 0)) := hRatio
  have hBaseFinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (chartBaseMap (equationIdeal p hp) j))) := by
    rw [← chartι_toBase]
    infer_instance
  have hCoeffFinite : (chartBaseMap (equationIdeal p hp) j).FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hBaseFinite
  obtain ⟨hDominant, hFinite, hCompact, hBase⟩ :=
    nativeLocalizedPencilAffineLine_dominant_finiteType001
      (chartBaseMap (equationIdeal p hp) j) hCoeffFinite g hCoeff (x 0) (x 1) hDenom hTrans
  let i : Spec (.of B) ⟶ hypersurface p hp :=
    Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι (equationIdeal p hp) j
  letI : IsOpenImmersion i := inferInstance
  let G : B →+* (hypersurface p hp).functionField :=
    IsLocalization.Away.lift (x 0) (isUnit_iff_ne_zero.mpr hDenom)
  letI : Nonempty (Spec (.of B)) :=
    ⟨Spec.map (CommRingCat.ofHom G) (IsLocalRing.closedPoint (hypersurface p hp).functionField)⟩
  have hIntegral : IsIntegral (Spec (.of B)) := isIntegral_of_isOpenImmersion i
  refine ⟨hDominant, hFinite, hCompact, inferInstance, hIntegral, ?_⟩
  rw [hBase]
  change Spec.map (CommRingCat.ofHom ((algebraMap R B).comp
    (chartBaseMap (equationIdeal p hp) j))) = i ≫ hypersurfaceToBase p hp
  dsimp only [i]
  change Spec.map (CommRingCat.ofHom ((algebraMap R B).comp
    (chartBaseMap (equationIdeal p hp) j))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι (equationIdeal p hp) j) ≫
        toBase (equationIdeal p hp)
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  rfl

end PfaffianDescent.Coray
