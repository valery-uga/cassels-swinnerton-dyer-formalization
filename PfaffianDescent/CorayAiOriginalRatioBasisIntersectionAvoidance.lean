import PfaffianDescent.CorayAiNativeRatioBasisIntersection
import PfaffianDescent.CorayAiOriginalNativePencilDominantAffineLine
import PfaffianDescent.CorayAiNativeBasisDenominator
import PfaffianDescent.CorayBoundedOriginalTangentIncidence

/-! SOURCE ONLY. Actual independent through-P/A sections construct the
ratio/fixed-full-basis intersection, with whole original image avoidance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary evaluation of the SAME auxiliary section derives native
normalized vanishing. No normalized-vanishing certificate is supplied. -/
private theorem originalAuxiliarySection_native_value_zero001
    {K L M : Type u} [Field K] [Field L] [Algebra K L]
    [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (hAux : cubicThroughPointAuxiliaryEvaluation p hp n y hpy
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) hpz s = 0) :
    gA (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0 := by
  obtain ⟨q, hq, _, hClass⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy s.1).mp s.2
  have hOrdinary : q.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
    change cubicCoordinateAlgebraEvaluation p hp
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) hpz s.1.1 = 0 at hAux
    rw [← hClass] at hAux
    exact hAux
  rw [← cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001
    p hp n y hpy j s q hq hClass]
  rw [MvPolynomial.hom_eval₂, hBase]
  exact hOrdinary

/-- Abstract native scalar compatibility computes the SAME basis numerator
without elaborating the original cubic/field/frame in the sum proof. -/
private theorem intersection_basis_numerator001
    {K V R : Type u} [Field K] [AddCommGroup V] [Module K V]
    [CommRing R] [Module K R]
    (e : V →ₗ[K] R) (f : K →+* R)
    (hScalar : ∀ (c : K) (r : R), c • r = f c * r)
    {m : ℕ} (b : Module.Basis (Fin m) K V) (v : V) :
    (∑ i, f (b.repr v i) * e (b i)) = e v := by
  have hEval := congrArg e (b.sum_repr v)
  rw [map_sum] at hEval
  calc
    _ = ∑ i, e (b.repr v i • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      exact (hScalar (b.repr v i) (e (b i))).symm
    _ = _ := hEval

/-- Native original generic evaluation of one actual nonzero section is
nonzero. This isolates its original scheme/scalar conversion once. -/
private theorem intersection_originalSection_generic_nonzero001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (v : cubicThroughCoordinateSections p hp n y hpy) (hv : v ≠ 0) :
    (show (hypersurface p hp).functionField from
      cubicThroughPointGenericLinearEvaluation p hp n y hpy j v) ≠ 0 := by
  have hInjective := cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0
  intro hZero
  have hEq : cubicThroughPointGenericLinearEvaluation p hp n y hpy j v =
      cubicThroughPointGenericLinearEvaluation p hp n y hpy j 0 := by
    change (show (hypersurface p hp).functionField from
      cubicThroughPointGenericLinearEvaluation p hp n y hpy j v) =
        (show (hypersurface p hp).functionField from
          cubicThroughPointGenericLinearEvaluation p hp n y hpy j 0)
    simpa only [map_zero] using hZero
  exact hv (hInjective hEq)

/-- Composition properties are proved over abstract schemes; the original
caller supplies previously constructed properties of its literal maps. -/
private theorem intersection_morphism_comp_properties001
    {U X S Y : Scheme.{u}} (k : U ⟶ X) (i : X ⟶ S) (f : X ⟶ Y)
    (hkOpen : IsOpenImmersion k) (hiOpen : IsOpenImmersion i)
    (hkDominant : IsDominant k) (hfDominant : IsDominant f)
    (hkFinite : LocallyOfFiniteType k) (hfFinite : LocallyOfFiniteType f)
    (hkCompact : QuasiCompact k) (hfCompact : QuasiCompact f) :
    IsOpenImmersion (k ≫ i) ∧ IsDominant (k ≫ f) ∧
      LocallyOfFiniteType (k ≫ f) ∧ QuasiCompact (k ≫ f) := by
  letI : IsOpenImmersion k := hkOpen
  letI : IsOpenImmersion i := hiOpen
  letI : IsDominant k := hkDominant
  letI : IsDominant f := hfDominant
  letI : LocallyOfFiniteType k := hkFinite
  letI : LocallyOfFiniteType f := hfFinite
  letI : QuasiCompact k := hkCompact
  letI : QuasiCompact f := hfCompact
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The actual base square is preserved by the actual restriction map.
Only ordinary abstract associativity is elaborated in this cut. -/
private theorem intersection_morphism_comp_base001
    {U X Y Z S : Scheme.{u}} (k : U ⟶ X) (f : X ⟶ Y) (i : X ⟶ Z)
    (b : Y ⟶ S) (p : Z ⟶ S) (h : f ≫ b = i ≫ p) :
    (k ≫ f) ≫ b = (k ≫ i) ≫ p := by
  simpa only [Category.assoc] using congrArg (fun r => k ≫ r) h

/-- The actual original pencil restriction properties, with the auxiliary
field/projective image frame absent. Every property is internally derived. -/
private theorem intersection_originalPencil_restriction_properties001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s) (a : Fin m) :
    let R := ChartRing (equationIdeal p hp) j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun k => e (b k)
    let x₀ := e (s 0)
    let B := Localization.Away x₀
    let C := Localization.Away (algebraMap R B (x a))
    let k := nativePencilBasisIntersectionToRatio001 x₀ (x a)
    let i₀ : Spec (.of B) ⟶ hypersurface p hp :=
      Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι (equationIdeal p hp) j
    let f₀ := nativeLocalizedPencilAffineLineMap001 (chartBaseMap (equationIdeal p hp) j)
      x₀ (e (s 1))
    IsIntegral (Spec (.of C)) ∧ IsOpenImmersion (k ≫ i₀) ∧
    IsDominant (k ≫ f₀) ∧ LocallyOfFiniteType (k ≫ f₀) ∧ QuasiCompact (k ≫ f₀) ∧
    (k ≫ f₀) ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) =
      (k ≫ i₀) ≫ hypersurfaceToBase p hp := by
  intro R e x x₀ B C k i₀ f₀
  letI : IsOpenImmersion (chartι (equationIdeal p hp) j) :=
    isOpenImmersion_chartι (equationIdeal p hp) j
  let g : R →+* (hypersurface p hp).functionField :=
    affineChartGenericEvaluation (chartι (equationIdeal p hp) j)
  have h₀ : g x₀ ≠ 0 := intersection_originalSection_generic_nonzero001
    p hp hp0 n y hpy j (s 0) (hli.ne_zero 0)
  have hₐ : g (x a) ≠ 0 := intersection_originalSection_generic_nonzero001
    p hp hp0 n y hpy j (b a) (b.linearIndependent.ne_zero a)
  obtain ⟨hD₀, hFT₀, hQC₀, hOI₀, hI₀, hB₀⟩ :=
    originalIndependentPencil_native_denominatorOpen_dominant_affineLine001
      p hp hp0 n y hpy j s hli
  letI : IsIntegral (Spec (.of B)) := hI₀
  obtain ⟨hIC, hOIk, hDk, hFTk, hQCk⟩ :=
    nativePencilBasisIntersection_integral_dominant_finiteType001 x₀ (x a) g h₀ hₐ
  obtain ⟨hOI, hD, hFT, hQC⟩ := intersection_morphism_comp_properties001
    k i₀ f₀ hOIk hOI₀ hDk hD₀ hFTk hFT₀ hQCk hQC₀
  have hOver := intersection_morphism_comp_base001 k f₀ i₀
    (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K))
    (hypersurfaceToBase p hp) hB₀
  exact ⟨hIC, hOI, hD, hFT, hQC, hOver⟩

/-- The actual original basis numerator is isolated without any auxiliary
field or projective-map frame. It computes the SAME native evaluation. -/
private theorem intersection_originalBasis_numerator001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (v : cubicThroughCoordinateSections p hp n y hpy) :
    (∑ i, chartBaseMap (equationIdeal p hp) j (b.repr v i) *
      cubicThroughPointChartEvaluation p hp n y hpy j (b i)) =
        cubicThroughPointChartEvaluation p hp n y hpy j v := by
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  have hEval := congrArg e (b.sum_repr v)
  rw [map_sum] at hEval
  calc
    _ = ∑ i, e (b.repr v i • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      exact (gradedChartNative_smul_eq_baseMap_mul (grading (equationIdeal p hp))
        (b.repr v i) (e (b i))).symm
    _ = _ := hEval

/-- Literal intersection on the SAME original cubic and SAME full basis.
Original through-P/A independence derives the A1 map; a fixed basis
coordinate nonzero at A selects the already prescribed chart. The entire
original field image rho is avoided at EVERY point of the intersection.
No dominance, finite type, source integrality, separation, attained-open,
member-integrality or dimension outcome is supplied. -/
theorem originalIndependentPencil_fixedBasisIntersection_avoids_auxiliaryImage001
    {K L M : Type u} [Field K] [Field L] [Algebra K L]
    [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (hAux : ∀ i, cubicThroughPointAuxiliaryEvaluation p hp n y hpy
      (fun k => gA (chartCoordinate (equationIdeal p hp) j k)) hpz (s i) = 0)
    (a : Fin m)
    (ha : gA (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0) :
    let R := ChartRing (equationIdeal p hp) j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun k => e (b k)
    let x₀ := e (s 0)
    let B := Localization.Away x₀
    let C := Localization.Away (algebraMap R B (x a))
    let k := nativePencilBasisIntersectionToRatio001 x₀ (x a)
    let gamma := nativePencilBasisIntersectionToBasis001 x₀ (x a)
    let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι (equationIdeal p hp) j
    let f₀ := nativeLocalizedPencilAffineLineMap001 (chartBaseMap (equationIdeal p hp) j)
      x₀ (e (s 1))
    let ell : Localization.Away (x a) →+* M :=
      IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
    let rho := Spec.map (CommRingCat.ofHom ell) ≫
      nativeLocalizedProjectiveChartPoint (chartBaseMap (equationIdeal p hp) j) x a
    let Phi := gamma ≫
      nativeLocalizedProjectiveChartPoint (chartBaseMap (equationIdeal p hp) j) x a
    IsIntegral (Spec (.of C)) ∧ IsOpenImmersion (k ≫ i₀) ∧
    IsDominant (k ≫ f₀) ∧ LocallyOfFiniteType (k ≫ f₀) ∧ QuasiCompact (k ≫ f₀) ∧
    (k ≫ f₀) ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) =
      (k ≫ i₀) ≫ hypersurfaceToBase p hp ∧
    gamma ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) =
      k ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
    (k ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))).opensRange =
      PrimeSpectrum.basicOpen x₀ ⊓ PrimeSpectrum.basicOpen (x a) ∧
    ∀ z : Spec (.of C), Phi z ≠ rho (IsLocalRing.closedPoint M) := by
  classical
  intro R e x x₀ B C k gamma i₀ f₀ ell rho Phi
  obtain ⟨hIC, hOI, hD, hFT, hQC, hOver⟩ :=
    intersection_originalPencil_restriction_properties001 p hp hp0 n y hpy j b s hli a
  obtain ⟨hSquare, hRange⟩ := nativePencilBasisIntersection_chart_square_range001 x₀ (x a)
  have hNumerator : (∑ i, chartBaseMap (equationIdeal p hp) j
      (b.repr (s 0) i) * x i) = x₀ :=
    intersection_originalBasis_numerator001 p hp n y hpy j b (s 0)
  have hA₀ : gA x₀ = 0 := originalAuxiliarySection_native_value_zero001
    p hp n y hpy j gA hBase hpz (s 0) (hAux 0)
  refine ⟨hIC, hOI, hD, hFT, hQC, hOver, hSquare, hRange, ?_⟩
  exact nativePencilBasisIntersection_avoids_entire_field_image001
    (chartBaseMap (equationIdeal p hp) j) x a x₀ (fun i => b.repr (s 0) i)
      hNumerator gA ha hA₀

end PfaffianDescent.Coray
