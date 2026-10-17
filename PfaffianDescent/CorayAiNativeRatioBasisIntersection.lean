import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Localization.Away.Basic

/-! SOURCE ONLY. Iterated localization realizes the literal intersection of
the ratio denominator and the fixed full-basis denominator. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The second native localization, retaining the actual ratio source. -/
def nativePencilBasisIntersectionToRatio001
    {R : Type u} [CommRing R] (x₀ xₐ : R) :
    Spec (.of (Localization.Away (algebraMap R (Localization.Away x₀) xₐ))) ⟶
      Spec (.of (Localization.Away x₀)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away x₀)
    (Localization.Away (algebraMap R (Localization.Away x₀) xₐ))))

/-- The named map remains a literal native localization open immersion,
with an explicit instance available while its range is elaborated. -/
instance nativePencilBasisIntersectionToRatio_isOpenImmersion001
    {R : Type u} [CommRing R] (x₀ xₐ : R) :
    IsOpenImmersion (nativePencilBasisIntersectionToRatio001 x₀ xₐ) := by
  unfold nativePencilBasisIntersectionToRatio001
  infer_instance

/-- Canonical fixed-basis chart hom; its coefficient map is the SAME
two actual localization maps, rather than a chosen scalar structure. -/
def nativePencilBasisIntersectionBasisHom001
    {R : Type u} [CommRing R] (x₀ xₐ : R) :
    Localization.Away xₐ →+*
      Localization.Away (algebraMap R (Localization.Away x₀) xₐ) :=
  IsLocalization.Away.lift xₐ
    (show IsUnit (((algebraMap (Localization.Away x₀)
      (Localization.Away (algebraMap R (Localization.Away x₀) xₐ))).comp
      (algebraMap R (Localization.Away x₀))) xₐ) from
        IsLocalization.Away.algebraMap_isUnit (algebraMap R (Localization.Away x₀) xₐ))

/-- Literal map from the intersection to the PRESCRIBED basis chart. -/
def nativePencilBasisIntersectionToBasis001
    {R : Type u} [CommRing R] (x₀ xₐ : R) :
    Spec (.of (Localization.Away (algebraMap R (Localization.Away x₀) xₐ))) ⟶
      Spec (.of (Localization.Away xₐ)) :=
  Spec.map (CommRingCat.ofHom (nativePencilBasisIntersectionBasisHom001 x₀ xₐ))

/-- Exact two charts commute back to the original coefficient chart;
the resulting opensRange is their literal intersection. -/
theorem nativePencilBasisIntersection_chart_square_range001
    {R : Type u} [CommRing R] (x₀ xₐ : R) :
    nativePencilBasisIntersectionToBasis001 x₀ xₐ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away xₐ))) =
        nativePencilBasisIntersectionToRatio001 x₀ xₐ ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away x₀))) ∧
    (nativePencilBasisIntersectionToRatio001 x₀ xₐ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away x₀)))).opensRange =
        PrimeSpectrum.basicOpen x₀ ⊓ PrimeSpectrum.basicOpen xₐ := by
  let B := Localization.Away x₀
  let C := Localization.Away (algebraMap R B xₐ)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R B))
  constructor
  · dsimp only [nativePencilBasisIntersectionToBasis001,
      nativePencilBasisIntersectionToRatio001]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    dsimp only [nativePencilBasisIntersectionBasisHom001]
    exact IsLocalization.Away.lift_comp xₐ
      (IsLocalization.Away.algebraMap_isUnit (algebraMap R B xₐ))
  · change (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ j₀).opensRange = _
    rw [Scheme.Hom.opensRange_comp]
    have hRangeK : (Spec.map (CommRingCat.ofHom (algebraMap B C))).opensRange =
        PrimeSpectrum.basicOpen (algebraMap R B xₐ) :=
      Scheme.Hom.opensRange_localizationAway (R := .of B) (algebraMap R B xₐ)
    rw [hRangeK]
    have hPreimage : j₀ ⁻¹ᵁ PrimeSpectrum.basicOpen xₐ =
        PrimeSpectrum.basicOpen (algebraMap R B xₐ) :=
      PrimeSpectrum.comap_basicOpen (algebraMap R B) xₐ
    rw [← hPreimage, j₀.image_preimage_eq_opensRange_inf]
    have hRangeJ : j₀.opensRange = PrimeSpectrum.basicOpen x₀ :=
      Scheme.Hom.opensRange_localizationAway (R := .of R) x₀
    rw [hRangeJ]

/-- A real generic field point in both denominator opens internally gives
nonemptiness, integrality, dominance, finite type and quasi-compactness of
the intersection inclusion. There is no assumed restriction outcome. -/
theorem nativePencilBasisIntersection_integral_dominant_finiteType001
    {R F : Type u} [CommRing R] [Field F]
    (x₀ xₐ : R) [IsIntegral (Spec (.of (Localization.Away x₀)))]
    (g : R →+* F) (h₀ : g x₀ ≠ 0) (hₐ : g xₐ ≠ 0) :
    IsIntegral (Spec (.of (Localization.Away (algebraMap R (Localization.Away x₀) xₐ)))) ∧
    IsOpenImmersion (nativePencilBasisIntersectionToRatio001 x₀ xₐ) ∧
    IsDominant (nativePencilBasisIntersectionToRatio001 x₀ xₐ) ∧
    LocallyOfFiniteType (nativePencilBasisIntersectionToRatio001 x₀ xₐ) ∧
    QuasiCompact (nativePencilBasisIntersectionToRatio001 x₀ xₐ) := by
  let B := Localization.Away x₀
  let C := Localization.Away (algebraMap R B xₐ)
  let G : B →+* F := IsLocalization.Away.lift x₀ (isUnit_iff_ne_zero.mpr h₀)
  have hG : G (algebraMap R B xₐ) ≠ 0 := by
    rw [IsLocalization.Away.lift_eq]
    exact hₐ
  let H : C →+* F := IsLocalization.Away.lift (algebraMap R B xₐ)
    (isUnit_iff_ne_zero.mpr hG)
  letI : Nonempty (Spec (.of C)) :=
    ⟨Spec.map (CommRingCat.ofHom H) (IsLocalRing.closedPoint F)⟩
  let k := nativePencilBasisIntersectionToRatio001 x₀ xₐ
  letI : IsOpenImmersion k := inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B C))))
  have hIntegral : IsIntegral (Spec (.of C)) := isIntegral_of_isOpenImmersion k
  letI : IsDominant k :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace k k.isOpenEmbedding.isOpenMap⟩
  have hFinite : (algebraMap B C).FiniteType := by
    apply RingHom.finiteType_algebraMap.mpr
    exact IsLocalization.finiteType_of_monoid_fg
      (Submonoid.powers (algebraMap R B xₐ)) C
  letI : LocallyOfFiniteType k :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hFinite
  letI : QuasiCompact k := inferInstance
  exact ⟨hIntegral, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Every point of the actual intersection avoids the ENTIRE original
projective image of a field point on the same prescribed basis chart.
The only value equations are the literal linear numerator and its
vanishing at that field point; no image separation is an input. -/
theorem nativePencilBasisIntersection_avoids_entire_field_image001
    {K R M : Type u} [CommRing K] [CommRing R] [Field M]
    {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (x₀ : R)
    (c : σ → K) (hNumerator : (∑ i, f (c i) * x i) = x₀)
    (gA : R →+* M) (hₐ : gA (x a) ≠ 0) (h₀ : gA x₀ = 0) :
    let ell : Localization.Away (x a) →+* M :=
      IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr hₐ)
    let rho := Spec.map (CommRingCat.ofHom ell) ≫ nativeLocalizedProjectiveChartPoint f x a
    let Phi := nativePencilBasisIntersectionToBasis001 x₀ (x a) ≫
      nativeLocalizedProjectiveChartPoint f x a
    ∀ z, Phi z ≠ rho (IsLocalRing.closedPoint M) := by
  classical
  intro ell rho Phi z hz
  let J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K) := ⊥
  let theta := nativeLocalizedProjectiveChartMap f x a
  let q := projectiveChartLinearForm a c
  let gamma := nativePencilBasisIntersectionToBasis001 x₀ (x a)
  let beta := nativePencilBasisIntersectionBasisHom001 x₀ (x a)
  let Aₐ := Spec.map (CommRingCat.ofHom ell) (IsLocalRing.closedPoint M)
  letI : IsOpenImmersion (chartι J a) := isOpenImmersion_chartι J a
  have hChart : Spec.map (CommRingCat.ofHom theta) (gamma z) =
      Spec.map (CommRingCat.ofHom theta) Aₐ := by
    apply (chartι J a).isOpenEmbedding.injective
    exact hz
  have hValue : ell (theta q) = 0 := by
    rw [(nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).2.2.1 c,
      hNumerator, map_mul, IsLocalization.Away.lift_eq, h₀, zero_mul]
  have hMemA : q ∈ (Spec.map (CommRingCat.ofHom theta) Aₐ).asIdeal := by
    change ell (theta q) ∈ (IsLocalRing.closedPoint M).asIdeal
    simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    exact hValue
  have hMem : theta q ∈ (gamma z).asIdeal := by
    change q ∈ (Spec.map (CommRingCat.ofHom theta) (gamma z)).asIdeal
    rw [hChart]
    exact hMemA
  have hNumeratorMem :=
    ((nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).2.2.2
      c (gamma z).asIdeal).mp hMem
  rw [hNumerator] at hNumeratorMem
  change beta (algebraMap R (Localization.Away (x a)) x₀) ∈ z.asIdeal at hNumeratorMem
  dsimp only [beta, nativePencilBasisIntersectionBasisHom001] at hNumeratorMem
  rw [IsLocalization.Away.lift_eq] at hNumeratorMem
  letI : z.asIdeal.IsPrime := z.isPrime
  exact (Ideal.notMem_of_isUnit z.asIdeal
    ((IsLocalization.Away.algebraMap_isUnit x₀).map
      (algebraMap (Localization.Away x₀)
        (Localization.Away (algebraMap R (Localization.Away x₀) (x a)))))) hNumeratorMem

end PfaffianDescent.Coray
