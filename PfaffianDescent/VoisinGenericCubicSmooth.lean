import PfaffianDescent.VoisinGenericFourLineSeparability
import PfaffianDescent.VoisinExplicitDiagonalSmooth
import AllCharacteristics.CubicPencilSmooth

/-!
# Smoothness of the tensor-generic cubic

The explicit diagonal cubic is a smooth specialization of the universal
cubic tensor. Smoothness is open in the universal coefficient space, so it
holds at the generic coefficient point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
open VoisinExplicitSeparableFourLineExample

universe u
attribute [local instance] PrimeSpectrum.isPrime

theorem universalCubicTensor_toMvPolynomial_map_diagonal
    (K : Type u) [Field K] [CharZero K] :
    ((universalCubicTensor K).toMvPolynomial).map
      (diagonalCubicTensorSpecialization K) = p₀ := by
  rw [cubic_toMvPolynomial_map, universalCubicTensor_map_diagonal,
    c₀_toMvPolynomial]

theorem genericCubicTensor_smooth
    (K : Type u) [Field K] [CharZero K] :
    Smooth (hypersurfaceToBase (genericCubicTensor K).toMvPolynomial
      (cubic_toMvPolynomial_isHomogeneous_three _)) := by
  let T := CubicTensorCoefficients K
  let L := FractionRing T
  let f : K →+* T := MvPolynomial.C
  let P : MvPolynomial (Fin 4) T := (universalCubicTensor K).toMvPolynomial
  let hp : P.IsHomogeneous 3 := cubic_toMvPolynomial_isHomogeneous_three _
  let g : T →+* L := algebraMap T L
  have hg : Function.Injective g := FaithfulSMul.algebraMap_injective T L
  let e₀ : T →+* K := diagonalCubicTensorSpecialization K
  let cA : Coefficients (Fin 4) 3 K →+* T :=
    MvPolynomial.eval₂Hom f
      (fun m : Monomials (Fin 4) 3 => P.coeff m.1)
  let x₀ : PrimeSpectrum T :=
    PrimeSpectrum.comap e₀ (IsLocalRing.closedPoint K)
  let η : PrimeSpectrum T :=
    PrimeSpectrum.comap g (IsLocalRing.closedPoint L)
  have he₀f : e₀.comp f = RingHom.id K := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact MvPolynomial.eval₂Hom_C (RingHom.id K) (c₀ (K := K)) a
  have he₀P : P.map e₀ = p₀ :=
    universalCubicTensor_toMvPolynomial_map_diagonal K
  have he₀cA : e₀.comp cA =
      coefficientSpecialization (d := 3) (RingHom.id K) p₀ := by
    have h := UniversalHomogeneous.coefficientEvaluation_comp
      (d := 3) f P e₀
    rw [he₀f, he₀P] at h
    simpa [cA, coefficientSpecialization] using h
  have hx₀ : PrimeSpectrum.comap cA x₀ ∈
      nonzeroSmoothParameterOpen K (Fin 4) 3 := by
    letI : Smooth (hypersurfaceToBase (p₀ (K := K)) p₀_homogeneous) := p₀_smooth
    have hmem := (equationParameter_mem_nonzeroSmooth_iff
      (d := 3) (RingHom.id K) p₀ p₀_homogeneous).2
      ⟨p₀_ne_zero, inferInstance⟩
    change PrimeSpectrum.comap cA
      (PrimeSpectrum.comap e₀ (IsLocalRing.closedPoint K)) ∈ _
    rw [← PrimeSpectrum.comap_comp_apply, he₀cA]
    exact hmem
  have hηideal : η.asIdeal = ⊥ := by
    rw [show η.asIdeal = RingHom.ker g from fieldPoint_asIdeal_eq_ker g]
    exact (RingHom.injective_iff_ker_eq_bot g).mp hg
  have hηle : η ≤ x₀ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, hηideal]
    exact bot_le
  have hspec : Specializes η x₀ :=
    (PrimeSpectrum.le_iff_specializes η x₀).mp hηle
  have hgeneric : PrimeSpectrum.comap cA η ∈
      nonzeroSmoothParameterOpen K (Fin 4) 3 :=
    (hspec.map (PrimeSpectrum.continuous_comap cA)).mem_open
      (nonzeroSmoothParameterOpen K (Fin 4) 3).2 hx₀
  have hgcA : g.comp cA =
      coefficientSpecialization (d := 3) (g.comp f) (P.map g) := by
    simpa [cA, coefficientSpecialization] using
      (UniversalHomogeneous.coefficientEvaluation_comp
        (d := 3) f P g)
  have hparam : equationParameter (g.comp f) (P.map g)
      (IsLocalRing.closedPoint L) ∈
        nonzeroSmoothParameterOpen K (Fin 4) 3 := by
    change PrimeSpectrum.comap
      (coefficientSpecialization (d := 3) (g.comp f) (P.map g))
      (IsLocalRing.closedPoint L) ∈ _
    rw [← hgcA, PrimeSpectrum.comap_comp_apply]
    exact hgeneric
  have hsmooth : Smooth (hypersurfaceToBase (P.map g) (hp.map g)) :=
    ((equationParameter_mem_nonzeroSmooth_iff (d := 3)
      (g.comp f) (P.map g) (hp.map g)).1 hparam).2
  have hP : P.map g = (genericCubicTensor K).toMvPolynomial := by
    exact cubic_toMvPolynomial_map g (universalCubicTensor K)
  exact (smooth_hypersurfaceToBase_congr
    (P.map g) (genericCubicTensor K).toMvPolynomial
    (hp.map g) (cubic_toMvPolynomial_isHomogeneous_three _) hP).mp hsmooth

/-- The generic smooth cubic stays smooth over every extension field,
including the algebraic closure used by the twelve-point witness. -/
theorem genericCubicTensor_smooth_baseChange
    (K : Type u) [Field K] [CharZero K]
    {F : Type u} [Field F]
    (φ : FractionRing (CubicTensorCoefficients K) →+* F) :
    Smooth (hypersurfaceToBase ((genericCubicTensor K).map φ).toMvPolynomial
      (cubic_toMvPolynomial_isHomogeneous_three _)) := by
  let p := (genericCubicTensor K).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three (genericCubicTensor K)
  letI : Smooth (hypersurfaceToBase p hp) := genericCubicTensor_smooth K
  have h := smooth_hypersurfaceToBase_map φ p hp
  exact (smooth_hypersurfaceToBase_congr
    (p.map φ) ((genericCubicTensor K).map φ).toMvPolynomial
    (hp.map φ) (cubic_toMvPolynomial_isHomogeneous_three _)
    (cubic_toMvPolynomial_map φ (genericCubicTensor K))).mp h

end PfaffianDescent
