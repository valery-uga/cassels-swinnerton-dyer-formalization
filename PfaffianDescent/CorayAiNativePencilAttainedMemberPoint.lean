import PfaffianDescent.CorayAiAffineLineNativeParameter
import PfaffianDescent.CorayAiOriginalNativePencilDominantAffineLine
import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Clearing the SAME already-inverted denominator gives the literal
member numerator x1-f(t)*x0, with no reduced-support substitution. -/
theorem nativeLocalizedPencilCoordinateMap_parameter_equation001
    {K R : Type u} [Field K] [CommRing R] (f : K →+* R) (x₀ x₁ : R) (t : K) :
    nativeLocalizedPencilCoordinateMap001 f x₀ x₁
      (MvPolynomial.X (default : ULift.{u} (Fin 1)) - MvPolynomial.C t) =
        algebraMap R (Localization.Away x₀) (x₁ - f t * x₀) * IsLocalization.Away.invSelf x₀ := by
  change Polynomial.eval₂ ((algebraMap R (Localization.Away x₀)).comp f)
    (algebraMap R (Localization.Away x₀) x₁ * IsLocalization.Away.invSelf x₀)
    ((MvPolynomial.uniqueAlgEquiv K (ULift.{u} (Fin 1)))
      (MvPolynomial.X default - MvPolynomial.C t)) = _
  simp only [MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply]
  rw [map_sub, map_mul, sub_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

/-- Chevalley attains a parameter in ORIGINAL K on the actual restricted
native ratio map. Its source point belongs to the literal member numerator.
The finite-type/dominance hypotheses are intermediate construction data;
the original caller obtains them from the native pencil producer. -/
theorem nativeLocalizedPencilAffineLine_exists_attained_memberPrime001
    {K R : Type u} [Field K] [Infinite K] [CommRing R]
    {T : Scheme.{u}} (f : K →+* R) (x₀ x₁ : R)
    (k : T ⟶ Spec (.of (Localization.Away x₀)))
    [IsDominant (k ≫ nativeLocalizedPencilAffineLineMap001 f x₀ x₁)]
    [LocallyOfFiniteType (k ≫ nativeLocalizedPencilAffineLineMap001 f x₀ x₁)]
    [QuasiCompact (k ≫ nativeLocalizedPencilAffineLineMap001 f x₀ x₁)] :
    ∃ (t : K) (z : T),
      algebraMap R (Localization.Away x₀) (x₁ - f t * x₀) ∈ (k z).asIdeal ∧
      (k ≫ nativeLocalizedPencilAffineLineMap001 f x₀ x₁) z =
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : ULift.{u} (Fin 1) => t))) ≫
            (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv)
          (IsLocalRing.closedPoint K) := by
  obtain ⟨q, hq, z, hz⟩ := dominant_affineSpace_exists_attained_rational_section001
    (k ≫ nativeLocalizedPencilAffineLineMap001 f x₀ x₁)
  obtain ⟨t, hParameter⟩ := affineLine_rationalSection_eq_native_parameter001 q hq
  rw [hParameter] at hz
  refine ⟨t, z, ?_, hz⟩
  let v := nativeLocalizedPencilCoordinateMap001 f x₀ x₁
  let ev := MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : ULift.{u} (Fin 1) => t)
  let ell := MvPolynomial.X (default : ULift.{u} (Fin 1)) - MvPolynomial.C t
  have hPrime : Spec.map (CommRingCat.ofHom v) (k z) =
      Spec.map (CommRingCat.ofHom ev) (IsLocalRing.closedPoint K) := by
    apply (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv.isOpenEmbedding.injective
    exact hz
  have hAtK : ell ∈ (Spec.map (CommRingCat.ofHom ev) (IsLocalRing.closedPoint K)).asIdeal := by
    change ev ell ∈ (IsLocalRing.closedPoint K).asIdeal
    simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
      ev, ell, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, RingHom.id_apply, sub_self]
  have hAtZ : v ell ∈ (k z).asIdeal := by
    change ell ∈ (Spec.map (CommRingCat.ofHom v) (k z)).asIdeal
    rw [hPrime]
    exact hAtK
  have hEquation := nativeLocalizedPencilCoordinateMap_parameter_equation001 f x₀ x₁ t
  change v ell = _ at hEquation
  rw [hEquation] at hAtZ
  have hMul := Ideal.mul_mem_right (algebraMap R (Localization.Away x₀) x₀) (k z).asIdeal hAtZ
  have hInv : IsLocalization.Away.invSelf x₀ * algebraMap R (Localization.Away x₀) x₀ = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf x₀
  rw [mul_assoc, hInv, mul_one] at hMul
  exact hMul

/-- A prime satisfying the literal native hyperplane equation lifts to an
ACTUAL point of the full scheme pullback, preserving its first projection. -/
theorem nativeLocalizedProjectiveHyperplanePullback_exists_point_above001
    {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K)
    (z : Spec (.of (Localization.Away (x a))))
    (hMem : nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ z.asIdeal) :
    let A := ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a))
    let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
    ∃ w : (pullback v h : Scheme), pullback.fst v h w = z := by
  classical
  intro A H v h
  have hTarget : v z ∈ Set.range h := by
    change PrimeSpectrum.comap (nativeLocalizedProjectiveChartMap f x a) z ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk H))
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    change H ≤ (PrimeSpectrum.comap (nativeLocalizedProjectiveChartMap f x a) z).asIdeal
    apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact hMem
  have hRange : z ∈ Set.range (pullback.fst v h) := by
    rw [Scheme.Pullback.range_fst]
    exact hTarget
  exact hRange

end PfaffianDescent.Coray
