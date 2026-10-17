import PfaffianDescent.CorayLiteralOriginalPairPolynomial
import PfaffianDescent.VoisinSmoothCubicEliminatedChart
import PfaffianDescent.CorayOriginalFunctionFieldTensorDomain
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Whole ORIGINAL cubic chart product has dimension at most four.
Its actual nonzero pair polynomial gives a whole quotient of dimension at
most three, preserving both full chart factors and their original K maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct nonZeroDivisors PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The literal original cubic chart is noetherian and has dimension<=2,
from its actual nonzero principal three-variable polynomial presentation. -/
theorem cubicOriginalChart_noetherian_and_ringKrullDim_le_two001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) (j : Fin 4) :
    IsNoetherianRing (ChartRing (equationIdeal p hp) j) ∧
      ringKrullDim (ChartRing (equationIdeal p hp) j) ≤ 2 := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  let σ := {i : Fin 4 // i ≠ j}
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let f : MvPolynomial σ K →ₐ[K] R := aeval (fun i => chartCoordinate I j i.1)
  obtain ⟨hf, hker, hq⟩ := PfaffianDescent.smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 j
  have hNoeth : IsNoetherianRing R := isNoetherianRing_of_surjective (MvPolynomial σ K) R f.toRingHom hf
  have hZero : f (coordinateOneEvaluation j p) = 0 := by
    have hMem : coordinateOneEvaluation j p ∈
        Ideal.span ({coordinateOneEvaluation j p} : Set (MvPolynomial σ K)) :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [← hker] at hMem
    exact hMem
  have hreg : coordinateOneEvaluation j p ∈ (MvPolynomial σ K)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hq
  have hcard : Fintype.card σ = 3 := by
    change Fintype.card {i : Fin 4 // ¬ i = j} = 3
    rw [Fintype.card_subtype_compl (fun i : Fin 4 => i = j)]
    simp
  have hDimSource : ringKrullDim (MvPolynomial σ K) = (3 : WithBot ℕ∞) := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, hcard, WithBot.coe_ofNat]
  have hsucc : ringKrullDim R + 1 ≤ (2 : WithBot ℕ∞) + 1 := by
    have h := ringKrullDim_succ_le_of_surjective f.toRingHom hf hreg hZero
    rw [hDimSource] at h
    convert h using 1 <;> norm_num
  exact ⟨hNoeth, ENat.WithBot.add_le_add_one_right_iff.mp hsucc⟩

private theorem tensorRightPolynomialMap_map001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {σ : Type} (x : σ → R) (q : MvPolynomial σ K) :
    (aeval (fun i => (1 : R) ⊗ₜ[K] x i) : MvPolynomial σ R →ₐ[R] R ⊗[K] R)
      (MvPolynomial.map (algebraMap K R) q) =
      (1 : R) ⊗ₜ[K] q.eval₂ (algebraMap K R) x := by
  let r : R →ₐ[K] R ⊗[K] R := Algebra.TensorProduct.includeRight
  have hCoeff : r.toRingHom.comp (algebraMap K R) = algebraMap K (R ⊗[K] R) :=
    RingHom.ext r.commutes
  have h := MvPolynomial.hom_eval₂ q (algebraMap K R) r.toRingHom x
  rw [hCoeff] at h
  change (MvPolynomial.map (algebraMap K R) q).eval₂ (algebraMap R (R ⊗[K] R))
    (fun i => (1 : R) ⊗ₜ[K] x i) = _
  rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq K R (R ⊗[K] R)]
  exact h.symm

private theorem tensorRightPolynomialMap_surjective001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {σ : Type} (x : σ → R)
    (heval : Function.Surjective (eval₂Hom (algebraMap K R) x)) :
    Function.Surjective (aeval (fun i => (1 : R) ⊗ₜ[K] x i) :
      MvPolynomial σ R →ₐ[R] R ⊗[K] R) := by
  classical
  let f : MvPolynomial σ R →ₐ[R] R ⊗[K] R := aeval (fun i => (1 : R) ⊗ₜ[K] x i)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero f⟩
  | tmul a b =>
    obtain ⟨q, hq⟩ := heval b
    have hPoly : f (MvPolynomial.map (algebraMap K R) q) = (1 : R) ⊗ₜ[K] b := by
      have h := tensorRightPolynomialMap_map001 x q
      have hValue : q.eval₂ (algebraMap K R) x = b := hq
      rw [hValue] at h
      exact h
    refine ⟨C a * MvPolynomial.map (algebraMap K R) q, ?_⟩
    have hC : f (C a) = a ⊗ₜ[K] (1 : R) := by
      simp [f, Algebra.TensorProduct.algebraMap_apply]
    rw [map_mul, hC, hPoly]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z w hz hw =>
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hw
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- The WHOLE original cubic chart tensor itself has dimension<=4.
Its second cubic is an actual nonzerodivisor in the polynomial algebra over
its first cubic chart: this is the six-variable/two-cubic quotient argument. -/
theorem cubicOriginalWholePairChart_ringKrullDim_le_four001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (hypersurface p hp)] (j : Fin 4)
    [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    let R := ChartRing (equationIdeal p hp) j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ringKrullDim (R ⊗[K] R) ≤ 4 := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  let σ := {i : Fin 4 // i ≠ j}
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let g : R →+* (hypersurface p hp).functionField := @affineChartGenericEvaluation
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hgOriginal : Function.Injective g := @affineChartGenericEvaluation_injective
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  letI : IsDomain R := hgOriginal.isDomain g
  obtain ⟨hNoeth, hDim⟩ := cubicOriginalChart_noetherian_and_ringKrullDim_le_two001 p hp hp0 j
  letI : IsNoetherianRing R := hNoeth
  let x : σ → R := fun i => chartCoordinate I j i.1
  let e : MvPolynomial σ K →ₐ[K] R := aeval x
  obtain ⟨he, hker, hq⟩ := PfaffianDescent.smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 j
  let f : MvPolynomial σ R →ₐ[R] R ⊗[K] R := aeval (fun i => (1 : R) ⊗ₜ[K] x i)
  have hf : Function.Surjective f := tensorRightPolynomialMap_surjective001 x he
  have hqZero : (coordinateOneEvaluation j p).eval₂ (algebraMap K R) x = 0 := by
    have hMem : coordinateOneEvaluation j p ∈
        Ideal.span ({coordinateOneEvaluation j p} : Set (MvPolynomial σ K)) :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [← hker] at hMem
    exact hMem
  let q := MvPolynomial.map (algebraMap K R) (coordinateOneEvaluation j p)
  have hq0 : q ≠ 0 := by
    intro h
    apply hq
    apply MvPolynomial.map_injective (algebraMap K R) (algebraMap K R).injective
    simpa using h
  have hZero : f q = 0 := by
    have h := tensorRightPolynomialMap_map001 x (coordinateOneEvaluation j p)
    rw [hqZero, TensorProduct.tmul_zero] at h
    exact h
  have hreg : q ∈ (MvPolynomial σ R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hq0
  have hcard : Fintype.card σ = 3 := by
    change Fintype.card {i : Fin 4 // ¬ i = j} = 3
    rw [Fintype.card_subtype_compl (fun i : Fin 4 => i = j)]
    simp
  have hSource : ringKrullDim (MvPolynomial σ R) ≤ (5 : WithBot ℕ∞) := by
    calc
      ringKrullDim (MvPolynomial σ R) = ringKrullDim R + 3 := by
        simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card,
          hcard, WithBot.coe_ofNat]
      _ ≤ (2 : WithBot ℕ∞) + 3 := _root_.add_le_add hDim le_rfl
      _ = 5 := by norm_num
  have hsucc : ringKrullDim (R ⊗[K] R) + 1 ≤ (4 : WithBot ℕ∞) + 1 := by
    have h := (ringKrullDim_succ_le_of_surjective f.toRingHom hf hreg hZero).trans hSource
    convert h using 1 <;> norm_num
  exact ENat.WithBot.add_le_add_one_right_iff.mp hsucc

/-- Geometric original integrality makes the WHOLE chart product a domain.
The actual original generic tensor map is proved injective by K-flatness. -/
theorem cubicOriginalWholePairChart_isDomain001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    let R := ChartRing (equationIdeal p hp) j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    IsDomain (R ⊗[K] R) := by
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  let F := (hypersurface p hp).functionField
  letI : Field F := inferInstanceAs (Field ((hypersurface p hp).functionField))
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let g : R →+* (hypersurface p hp).functionField := @affineChartGenericEvaluation
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hgOriginal : Function.Injective g := @affineChartGenericEvaluation_injective
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hBase : g.comp (chartBaseMap I j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  let gAlg : R →ₐ[K] F := { toRingHom := g, commutes' := fun t => RingHom.congr_fun hBase t }
  have hg : Function.Injective gAlg := hgOriginal
  letI : IsDomain (F ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := F) p hp hp0
  have hTensor : Function.Injective (Algebra.TensorProduct.map gAlg gAlg) := by
    exact TensorProduct.map_injective_of_flat_flat gAlg.toLinearMap gAlg.toLinearMap hg hg
  exact hTensor.isDomain (Algebra.TensorProduct.map gAlg gAlg).toRingHom

/-- Every actual nonzero pair equation cuts the WHOLE original chart product
to dimension<=3. The constructed literal pair polynomial supplies Q!=0. -/
theorem cubicOriginalWholePairChart_nonzeroEquation_ringKrullDim_le_three001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] :
    let R := ChartRing (equationIdeal p hp) j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ Q : R ⊗[K] R, Q ≠ 0 →
      ringKrullDim ((R ⊗[K] R) ⧸ Ideal.span ({Q} : Set (R ⊗[K] R))) ≤ 3 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  letI : IsDomain (R ⊗[K] R) := cubicOriginalWholePairChart_isDomain001 p hp hp0 j
  change ∀ Q : R ⊗[K] R, Q ≠ 0 →
    ringKrullDim ((R ⊗[K] R) ⧸ Ideal.span ({Q} : Set (R ⊗[K] R))) ≤ 3
  intro Q hQ
  have hreg : Q ∈ (R ⊗[K] R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hQ
  have hsucc : ringKrullDim ((R ⊗[K] R) ⧸ Ideal.span ({Q} : Set (R ⊗[K] R))) + 1 ≤
      (3 : WithBot ℕ∞) + 1 := by
    have h := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg).trans
      (cubicOriginalWholePairChart_ringKrullDim_le_four001 p hp hp0 j)
    convert h using 1 <;> norm_num
  exact ENat.WithBot.add_le_add_one_right_iff.mp hsucc

/-- Natural ORIGINAL data constructs the same literal pair polynomial,
retains the exact first-point whole-jet relation and proves that its WHOLE
pair-chart quotient has dimension<=3. Q!=0 is constructed internally. -/
theorem cubicThroughPointBasis_exists_literalBadPairEquation_dimension_le_three001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    let F := (hypersurface p hp).functionField
    letI : Field F := inferInstanceAs (Field ((hypersurface p hp).functionField))
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let g : R →+* F := @affineChartGenericEvaluation
      R (inferInstance : CommRing R)
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let z : Fin 4 → F := fun i => g (chartCoordinate I j i)
    ∃ pivot : Fin 3,
      let v : Fin 2 → Fin 4 → F := fun r i =>
        PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
      ∃ (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v) = 0)
        (hAnchor : surfacePlaneJetCoordinates z v j = 1),
      ∃ (d : R) (A : Fin m → R) (P : MvPolynomial (Fin 4 ⊕ Fin 4) K),
        g d ≠ 0 ∧
        (∑ i, g (A i) • cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor (e (b i))) = 0 ∧
        P.eval₂ (algebraMap K (R ⊗[K] R))
          (Sum.elim (fun i => chartCoordinate I j i ⊗ₜ[K] (1 : R))
            (fun i => (1 : R) ⊗ₜ[K] chartCoordinate I j i)) = ∑ i, A i ⊗ₜ[K] e (b i) ∧
        P.eval₂ (algebraMap K (R ⊗[K] R))
          (Sum.elim (fun i => chartCoordinate I j i ⊗ₜ[K] (1 : R))
            (fun i => (1 : R) ⊗ₜ[K] chartCoordinate I j i)) ≠ 0 ∧
        ringKrullDim ((R ⊗[K] R) ⧸ Ideal.span
          ({P.eval₂ (algebraMap K (R ⊗[K] R))
            (Sum.elim (fun i => chartCoordinate I j i ⊗ₜ[K] (1 : R))
              (fun i => (1 : R) ⊗ₜ[K] chartCoordinate I j i))} : Set (R ⊗[K] R))) ≤ 3 := by
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  let F := (hypersurface p hp).functionField
  letI : Field F := inferInstanceAs (Field ((hypersurface p hp).functionField))
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  obtain ⟨pivot, hpJ, hAnchor, d, A, P, hd, hJet, hP, hQ⟩ :=
    cubicThroughPointBasis_genericNativeJet_exists_literalOriginalPairPolynomial001
      p hp hp0 n y hpy j b hsize
  refine ⟨pivot, hpJ, hAnchor, d, A, P, hd, hJet, hP, hQ, ?_⟩
  exact cubicOriginalWholePairChart_nonzeroEquation_ringKrullDim_le_three001
    p hp hp0 j _ hQ

end PfaffianDescent.Coray
