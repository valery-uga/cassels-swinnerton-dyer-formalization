import PfaffianDescent.CorayOriginalJetPairSpecializationPivot
import PfaffianDescent.CorayOriginalNativePrincipalRankSmoothGoodOpen
import PfaffianDescent.CorayOriginalWholePairNonzeroEquationBadLineKernel
import PfaffianDescent.CorayUniversalNativeTangentIncidence

/-! FIXED actual Principal tuple: the natural leastpoint/window caller
constructs H/rankPivot/i/t/fS internally and passes that EXACT tuple here.
This cut constructs own pair/Q/uPair/v/F/bad internally, making no new
principal, rank pivot, basis, chart, image factor or boundary choice. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Retain the EXACT genuinely constructed actual Principal tuple.
Original freedom constructs the own pair tuple, then v=uPair*THAT H and
its SAME whole Q/F/badline kernel polynomial. The final natural caller
supplies H/rankPivot/i/t/fS from its own actual Principal producer; no
rank/open/factor existence is replaced by an assumption there. -/
theorem cubicThroughPointBasis_exists_pairBadLineGuard_for_sameActualPrincipalTuple001
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let FF := S.functionField
    letI : Algebra K FF := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
      S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
    let x := chartCoordinate I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let gradient : Fin 3 → R := fun t => (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
    ∀ (rankPivot : Fin 3) (H : R) (i t : Fin m)
      (fS : Spec (.of (Localization.Away (e (b a)))) ⟶
        cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a),
      g H ≠ 0 →
      originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot (fun l => e (b l)) a i t H →
      Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) →
      fS ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
        nativeLocalizedProjectiveChartPoint (chartBaseMap I j) (fun l => e (b l)) a →
      fS ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) ≫
          hypersurfaceToBase p hp →
      (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) →
      (∀ s : Spec (.of (Localization.Away (e (b a)))),
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) s ∈
          (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) →
        fS s ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a) →
    ∃ (pairPivot : Fin 3) (d : R) (A : Fin m → R)
      (q : Fin m → MvPolynomial (Fin 4) K) (P : MvPolynomial (Fin 4 ⊕ Fin 4) K) (k : Fin m),
      (∀ l, (q l).IsHomogeneous n ∧ (q l).eval₂ (algebraMap K L) y = 0 ∧
        Ideal.Quotient.mk I.toIdeal (q l) = (b l).1.1 ∧
        (q l).eval₂ (algebraMap K R) x = e (b l)) ∧
      gradient pairPivot ≠ 0 ∧
      let uPair := d * gradient pairPivot * A k
      let v := uPair * H
      g uPair ≠ 0 ∧ g H ≠ 0 ∧ g v ≠ 0 ∧
      originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot (fun l => e (b l)) a i t H ∧
      Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) ∧
      (∀ (M : Type u) [Field M] [Algebra K M] (h : R →ₐ[K] M), h v ≠ 0 →
        h uPair ≠ 0 ∧ h H ≠ 0 ∧ h (gradient pairPivot) ≠ 0 ∧
        (fun l => h (A l)) ≠ 0 ∧
        (∑ l, h (A l) • (q l).eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun l => h (x l))
            (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
              (fun s => h (gradient s)) pairPivot l r))) = 0) ∧
      (fS ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
          nativeLocalizedProjectiveChartPoint (chartBaseMap I j) (fun l => e (b l)) a ∧
        fS ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) ≫
            hypersurfaceToBase p hp ∧
        (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) ⊆
          Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) ∧
        ∀ s : Spec (.of (Localization.Away (e (b a)))),
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) s ∈
            (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) →
          fS s ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a) ∧
      let T := R ⊗[K] R
      let Q : T := ∑ l, A l ⊗ₜ[K] e (b l)
      let F : T := Q * (v ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v)
      P.eval₂ (algebraMap K T)
        (Sum.elim (fun l => x l ⊗ₜ[K] (1 : R)) (fun l => (1 : R) ⊗ₜ[K] x l)) = Q ∧
      Q ≠ 0 ∧ F ≠ 0 ∧ ringKrullDim (T ⧸ Ideal.span ({F} : Set T)) ≤ 3 ∧
      let B := T ⧸ Ideal.span ({F} : Set T)
      let xy := cubicOriginalWholePairChartAmbientVectors p hp j
      let xB := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.1
      let yB := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.2
      let D := originalPairGrassmannMinor rho xB yB
      let C := Localization.Away D
      let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho xB)
      let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho yB)
      let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf D)
      ∃ bad : GrassmannianChartRing K 2 2, bad ≠ 0 ∧
        (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)) bad = 0 ∧
        closure (Set.range (originalPairMinorOpenToGrassmann (K := K) rho xB yB)) ≠
          (Set.univ : Set (grassmannianScheme K 2 2)) := by
  trace "FIXEDHREUSE_ENTRY"
  classical
  trace "FIXEDHREUSE_BEFORE_CLEAN_PAIR_HAVE"
  have hPairPackage := cubicThroughPointBasis_exists_originalPairEquation_nativeJet_principalOpen_withPivot001
    p hp hp0 n y hpy j b hsize
  trace "FIXEDHREUSE_AFTER_CLEAN_PAIR_HAVE"
  intro S I R FF g x e gradient
  trace "FIXEDHREUSE_AFTER_HEADER_ALIASES"
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  letI : Field FF := inferInstanceAs (Field ((hypersurface p hp).functionField))
  letI : Algebra K FF := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  trace "FIXEDHREUSE_AFTER_NATIVE_INSTANCES"
  intro rankPivot H i t fS hH hRank hDense hFactor hBase hCover hSmooth
  trace "FIXEDHREUSE_AFTER_TUPLE_INTROS"
  have hg : Function.Injective g := @affineChartGenericEvaluation_injective R (inferInstance : CommRing R)
    S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  trace "FIXEDHREUSE_AFTER_GENERIC_INJECTIVITY"
  trace "FIXEDHREUSE_BEFORE_PAIR_OBTAIN"
  obtain ⟨pairPivot, d, A, q, P, k, hRep, hP, hQ, _hValue, _hDirections, hPivot, huPair, _hOpen, hPoints⟩ :=
    hPairPackage
  trace "FIXEDHPAIR_AFTER_PAIR_PRODUCER"
  let uPair := d * gradient pairPivot * A k
  let v := uPair * H
  have hGuPair : g uPair ≠ 0 := by
    intro hz
    apply huPair
    apply hg
    simpa only [map_zero] using hz
  have hGv : g v ≠ 0 := by
    change g (uPair * H) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hGuPair hH
  have hv : v ≠ 0 := by
    intro hz
    exact hGv (by rw [hz, map_zero])
  trace "FIXEDHPAIR_AFTER_PRINCIPAL_NONZERO"
  let T := R ⊗[K] R
  let Q : T := ∑ l, A l ⊗ₜ[K] e (b l)
  let F : T := Q * (v ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v)
  letI : IsDomain T := cubicOriginalWholePairChart_isDomain001 p hp hp0 j
  trace "FIXEDHPAIR_AFTER_TENSOR_ALIASES"
  have hQnonzero : Q ≠ 0 := by
    change (∑ l, A l ⊗ₜ[K] e (b l)) ≠ 0
    rw [← hP]
    exact hQ
  have hFnonzero : F ≠ 0 := originalPairEquation_withPrincipalOpenBoundary_ne_zero001 Q hQnonzero v hv
  trace "FIXEDHPAIR_AFTER_NONZERO_EQUATIONS"
  have hDimension := cubicOriginalWholePairChart_nonzeroEquation_ringKrullDim_le_three001 p hp hp0 j F hFnonzero
  trace "FIXEDHPAIR_AFTER_DIMENSION"
  have hBadLine := cubicOriginalWholePairChart_nonzeroEquation_exists_actualBadLineEquation001
    p hp hp0 j rho F hFnonzero
  trace "FIXEDHPAIR_AFTER_BADLINE_PRODUCER"
  refine ⟨pairPivot, d, A, q, P, k,
    hRep, hPivot, hGuPair, hH, hGv, hRank, hDense, ?_, ?_, hP, hQnonzero, hFnonzero, hDimension, hBadLine⟩
  · trace "FIXEDHPAIR_CALLBACK_ENTRY"
    intro M _ _ h hV
    have hUPair : h uPair ≠ 0 := by
      intro hz
      apply hV
      change h (uPair * H) = 0
      rw [map_mul, hz, zero_mul]
    have hHH : h H ≠ 0 := by
      intro hz
      apply hV
      change h (uPair * H) = 0
      rw [map_mul, hz, mul_zero]
    trace "FIXEDHPAIR_CALLBACK_BEFORE_NATIVE"
    have hNative := hPoints M h hUPair
    trace "FIXEDHPAIR_CALLBACK_AFTER_NATIVE"
    exact ⟨hUPair, hHH, hNative.1, hNative.2.1, hNative.2.2.1⟩
  · trace "FIXEDHPAIR_FINAL_FACTOR_ENTRY"
    exact ⟨hFactor, hBase, hCover, hSmooth⟩

end PfaffianDescent.Coray
