import PfaffianDescent.CorayGeometricJetPairIncidenceNonvanishing
import PfaffianDescent.CorayOriginalAffinePairCommonDenominator
import AllCharacteristics.NormalizedChartGeneration
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.TensorProduct.Maps

/-! A literal ORIGINAL-K nonzero pair polynomial on the SAME original cubic
chart product, with a proved vanishing first-point surface-jet relation. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem pairTensor_clearing_ne_zero001
    {K R F : Type u} [Field K] [CommRing R] [Field F]
    [Algebra K R] [Algebra K F] (g : R →ₐ[K] F)
    {m : ℕ} (d : R) (A t : Fin m → R) (c : Fin m → F)
    (hd : g d ≠ 0) (hA : ∀ i, g (A i) = g d * c i)
    (hTensor : (∑ i, c i ⊗ₜ[K] g (t i) : F ⊗[K] F) ≠ 0) :
    (∑ i, A i ⊗ₜ[K] t i : R ⊗[K] R) ≠ 0 := by
  have hMap : Algebra.TensorProduct.map g g (∑ i, A i ⊗ₜ[K] t i) =
      (g d ⊗ₜ[K] (1 : F)) * (∑ i, c i ⊗ₜ[K] g (t i)) := by
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hA]
  have hUnit : IsUnit (g d ⊗ₜ[K] (1 : F)) :=
    (isUnit_iff_ne_zero.mpr hd).map (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] F)
  intro hZero
  have h := congrArg (Algebra.TensorProduct.map g g) hZero
  rw [hMap, map_zero] at h
  exact hTensor (hUnit.mul_right_eq_zero.mp h)

/-- Polynomial generation in each original chart constructs the literal
original-K pair polynomial for any given finite tensor sum. -/
theorem pairChartTensorSum_exists_originalPolynomial001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    (x : Fin 4 → R)
    (heval : Function.Surjective (eval₂Hom (algebraMap K R) x))
    {m : ℕ} (A t : Fin m → R) :
    ∃ P : MvPolynomial (Fin 4 ⊕ Fin 4) K,
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R))
          (fun i => (1 : R) ⊗ₜ[K] x i)) = ∑ i, A i ⊗ₜ[K] t i := by
  classical
  choose alpha hAlpha using fun i => heval (A i)
  choose beta hBeta using fun i => heval (t i)
  let l : R →ₐ[K] R ⊗[K] R := Algebra.TensorProduct.includeLeft
  let r : R →ₐ[K] R ⊗[K] R := Algebra.TensorProduct.includeRight
  have hLeft (q : MvPolynomial (Fin 4) K) :
      q.eval₂ (algebraMap K (R ⊗[K] R)) (fun i => x i ⊗ₜ[K] (1 : R)) =
        q.eval₂ (algebraMap K R) x ⊗ₜ[K] (1 : R) := by
    have h := MvPolynomial.hom_eval₂ q (algebraMap K R) l.toRingHom x
    have hCoeff : l.toRingHom.comp (algebraMap K R) = algebraMap K (R ⊗[K] R) :=
      RingHom.ext l.commutes
    rw [hCoeff] at h
    exact h.symm
  have hRight (q : MvPolynomial (Fin 4) K) :
      q.eval₂ (algebraMap K (R ⊗[K] R)) (fun i => (1 : R) ⊗ₜ[K] x i) =
        (1 : R) ⊗ₜ[K] q.eval₂ (algebraMap K R) x := by
    have h := MvPolynomial.hom_eval₂ q (algebraMap K R) r.toRingHom x
    have hCoeff : r.toRingHom.comp (algebraMap K R) = algebraMap K (R ⊗[K] R) :=
      RingHom.ext r.commutes
    rw [hCoeff] at h
    exact h.symm
  refine ⟨∑ i, (MvPolynomial.rename Sum.inl (alpha i)) *
    (MvPolynomial.rename Sum.inr (beta i)), ?_⟩
  simp only [eval₂_sum, eval₂_mul, eval₂_rename]
  change (∑ i, (alpha i).eval₂ (algebraMap K (R ⊗[K] R))
      (fun j => x j ⊗ₜ[K] (1 : R)) *
      (beta i).eval₂ (algebraMap K (R ⊗[K] R))
      (fun j => (1 : R) ⊗ₜ[K] x j)) = _
  apply Finset.sum_congr rfl
  intro i _
  have hAE : (alpha i).eval₂ (algebraMap K R) x = A i := hAlpha i
  have hBE : (beta i).eval₂ (algebraMap K R) x = t i := hBeta i
  rw [hLeft, hRight, hAE, hBE]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem weightedJet_clearCoefficients001
    {R F J : Type u} [CommRing R] [Field F] [AddCommMonoid J] [Module F J]
    (g : R →+* F) {m : ℕ} (d : R) (A : Fin m → R) (c : Fin m → F) (w : Fin m → J)
    (hA : ∀ i, g (A i) = g d * c i) (hJet : (∑ i, c i • w i) = 0) :
    (∑ i, g (A i) • w i) = 0 := by
  calc
    (∑ i, g (A i) • w i) = ∑ i, g d • (c i • w i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i, mul_smul]
    _ = g d • (∑ i, c i • w i) := by rw [Finset.smul_sum]
    _ = 0 := by rw [hJet, smul_zero]

private theorem coefficientTensorSum_ne_zero001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {m : ℕ} (t c : Fin m → F)
    (hli : LinearIndependent F (fun i => ((1 : F) ⊗ₜ[K] t i : F ⊗[K] F)))
    (hc : c ≠ 0) : (∑ i, c i ⊗ₜ[K] t i : F ⊗[K] F) ≠ 0 := by
  intro hZero
  have hSum : (∑ i, c i • ((1 : F) ⊗ₜ[K] t i)) = 0 := by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hZero
  exact hc (funext (Fintype.linearIndependent_iff.mp hli c hSum))

private theorem genericJet_pairPolynomial_from_actualFractions001
    {K R F : Type u} [Field K] [CommRing R] [Field F]
    [Algebra K R] [Algebra K F]
    (g : R →ₐ[K] F) (gJ : R →+* SurfacePlaneJet F)
    {m : ℕ} (t : Fin m → R) (hm : 3 < m)
    (hli : LinearIndependent F (fun i => ((1 : F) ⊗ₜ[K] g (t i) : F ⊗[K] F)))
    (hFractions : ∀ c : Fin m → F, ∃ d : R, g d ≠ 0 ∧
      ∃ A : Fin m → R, ∀ i, g (A i) = g d * c i)
    (x : Fin 4 → R)
    (heval : Function.Surjective (eval₂Hom (algebraMap K R) x)) :
    ∃ (d : R) (A : Fin m → R) (P : MvPolynomial (Fin 4 ⊕ Fin 4) K),
      g d ≠ 0 ∧ (∑ i, g (A i) • gJ (t i)) = 0 ∧
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R)) (fun i => (1 : R) ⊗ₜ[K] x i)) =
          ∑ i, A i ⊗ₜ[K] t i ∧
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R)) (fun i => (1 : R) ⊗ₜ[K] x i)) ≠ 0 := by
  obtain ⟨c, hc, hJet⟩ := surfacePlaneJet_values_exists_nonzero_hyperplane001 hm (fun i => gJ (t i))
  obtain ⟨d, hd, A, hA⟩ := hFractions c
  have hCoefJet := weightedJet_clearCoefficients001 g.toRingHom d A c (fun i => gJ (t i)) hA hJet
  have hTensor := coefficientTensorSum_ne_zero001 (fun i => g (t i)) c hli hc
  have hPair := pairTensor_clearing_ne_zero001 g d A t c hd hA hTensor
  obtain ⟨P, hP⟩ := pairChartTensorSum_exists_originalPolynomial001 x heval A t
  refine ⟨d, A, P, hd, hCoefJet, hP, ?_⟩
  rw [hP]
  exact hPair

/-- Algebra laws for the EXISTING native chart action. The scalar operation
is retained; the actual chartBaseMap multiplication law proves compatibility. -/
@[instance_reducible]
def cubicChartNativeAlgebra
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    Algebra K (ChartRing (equationIdeal p hp) j) where
  toSMul := inferInstance
  algebraMap := chartBaseMap (equationIdeal p hp) j
  commutes' c x := mul_comm _ _
  smul_def' c x := gradedChartNative_smul_eq_baseMap_mul (grading (equationIdeal p hp)) c x

/-- Natural ORIGINAL cubic data constructs a literal original-K pair
polynomial which does not vanish on the WHOLE original chart product, and
whose second-point basis equation annihilates the full first-point jet.
No polynomial, denominator, hyperplane or incidence-nonvanishing premise
is supplied. This is the proper pair condition before good-line selection. -/
theorem cubicThroughPointBasis_genericNativeJet_exists_literalOriginalPairPolynomial001
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
            (fun i => (1 : R) ⊗ₜ[K] chartCoordinate I j i)) ≠ 0 := by
  classical
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
  have hBase : g.comp (chartBaseMap I j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  let gAlg : R →ₐ[K] F := { toRingHom := g, commutes' := fun t => RingHom.congr_fun hBase t }
  obtain ⟨_hpz, pivot, _hpivot, hpJ, hAnchor⟩ :=
    smoothOriginalCubic_chartFieldPoint_exists_nativeFullJet001 p hp hp0 j g hBase
  let v : Fin 2 → Fin 4 → F := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
  let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  have hRank := cubicThroughCoordinateSections_finrank_ge_five p hp hp0 n y hpy hsize
  have hm : 3 < m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at hRank
    omega
  have hli : LinearIndependent F
      (fun i => ((1 : F) ⊗ₜ[K] g (e (b i)) : F ⊗[K] F)) :=
    cubicThroughPointBasisTensorCoordinates_linearIndependent (B := F) p hp hp0 n y hpy j b
  have hFractions : ∀ c : Fin m → F, ∃ d : R, gAlg d ≠ 0 ∧
      ∃ A : Fin m → R, ∀ i, gAlg (A i) = gAlg d * c i := by
    intro c
    exact @affineChartGenericEvaluation_commonDenominator001
      R (inferInstance : CommRing R)
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange)) m c
  have heval : Function.Surjective (eval₂Hom (algebraMap K R) (chartCoordinate I j)) :=
    eval₂_chartCoordinate_surjective I j
  obtain ⟨d, A, P, hd, hCoefJet, hP, hPair⟩ :=
    genericJet_pairPolynomial_from_actualFractions001 gAlg gJ (fun i => e (b i)) hm
      hli hFractions (chartCoordinate I j) heval
  exact ⟨pivot, hpJ, hAnchor, d, A, P, hd, hCoefJet, hP, hPair⟩

end PfaffianDescent.Coray
