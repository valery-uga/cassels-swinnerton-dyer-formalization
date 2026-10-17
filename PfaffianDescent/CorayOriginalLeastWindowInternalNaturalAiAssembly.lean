import Mathlib.Tactic.Trace
import PfaffianDescent.CorayOriginalLeastWindowPrincipalPairBadLineAssembly
import PfaffianDescent.CorayOriginalExistingJointGuardGenuineAuxiliarySelector
import PfaffianDescent.CorayOriginalStrictWindowDerivedIntegralFamilyNaturalAiEndpoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine natural Ai assembly from ONLY the original least-point window.
One canonical chart/full basis/denominator, one principal tuple, one aligned
permutation and ONE whole pair guard are constructed internally. The same
badline kernel selects the literal auxiliary degree-three field/cut and an
ORIGINAL-K tangent section. Its SAME original q/AX regularity and full degree,
whole integrality, full-constants normalization argument and smaller original
point contradict leastness. No auxiliary point, splitting field, selected
matrix/section/q/curve point, jet/rank/open/guard, integral-family, regularity,
GI/normalization or smaller-point outcome is a premise. -/
theorem coray_leastOriginalPoint_noSection_window_eq_four_or_ten_internalAi001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2) :
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) := by
  classical
  trace "FINAL_AI_6370_ENTRY"
  have hNaturalPair := coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_samePrincipal_pairBadLineGuard001
    p hp hp0 P hPointCoprime hleast hno n hLower hUpper
  trace "FINAL_AI_6370_AFTER_CLEAN_NATURAL_PAIR_HAVE"
  let S := hypersurface p hp
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  trace "FINAL_AI_6370_AFTER_ORIGINAL_INSTANCES"
  rcases hNaturalPair with hFour | hTen | hResidual
  · exact Or.inl hFour
  · exact Or.inr hTen
  trace "FINAL_AI_6370_AFTER_PAIR_CASES"
  rcases hResidual with ⟨hnThree, _hLarge, hStrict, _hFreedom, _hSize,
    j, gP, hPBase, hPMap, hpy, hChart, m, _hFive, b, a,
    _hE, rankPivot, H, i, k, _hH, hRank, _hDense, _f, _hFactor, _hBase, _hCover, _hSmooth,
    rho, hRho, pairPivot, d, pairCoefficients, q, _Ppair, kPair, hRepresentatives, _hGamma,
    _hUPair, _hHAgain, hVGeneric, _hRankAgain, _hDenseAgain, hPoints, _hRetainedImage,
    _hPairPolynomial, _hQNonzero, _hFNonzero, _hPairDimension, bad, hBadNonzero, hFullKernel, _hBadClosed⟩
  trace "FINAL_AI_6370_AFTER_PAIR_OBTAIN"
  letI : Nonempty (chartι (equationIdeal p hp) j).opensRange := hChart
  let I := equationIdeal p hp
  let R := ChartRing I j
  let L := S.residueField P.1
  let y : Fin 4 → L := fun l => gP (chartCoordinate I j l)
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let x := chartCoordinate I j
  let gradient : Fin 3 → R := fun l => (pderiv (j.succAbove l) p).eval₂ (algebraMap K R) x
  let uPair := d * gradient pairPivot * pairCoefficients kPair
  let v : R := uPair * H
  let genericEvaluation := @affineChartGenericEvaluation R (inferInstance : CommRing R)
    S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstance : Nonempty (chartι I j).opensRange)
  trace "FINAL_AI_6370_AFTER_LITERAL_CHART_ACTIONS"
  have hv : v ≠ 0 := by
    intro hz
    apply hVGeneric
    change genericEvaluation v = 0
    rw [hz, map_zero]
  trace "FINAL_AI_6370_AFTER_GUARD_NONZERO"
  have hRep : ∀ t, Ideal.Quotient.mk I.toIdeal (q t) = (b t).1.1 :=
    fun t => (hRepresentatives t).2.2.1
  trace "FINAL_AI_6370_AFTER_QUOTIENT_REPRESENTATIVES"
  let M := AlgebraicClosure K
  letI : IsSepClosed M := inferInstance
  trace "FINAL_AI_6370_AFTER_INTERNAL_SPLITTING_FIELD"
  have hPointSelector : ∀ h : R →ₐ[K] M, h v ≠ 0 →
      h H ≠ 0 ∧ h (gradient pairPivot) ≠ 0 ∧
      (∑ t, h (pairCoefficients t) • (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates (fun l => h (x l))
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun s => h (gradient s)) pairPivot l r))) = 0 := by
    intro h hh
    have hData := hPoints M h hh
    exact ⟨hData.2.1, hData.2.2.1, hData.2.2.2.2⟩
  trace "FINAL_AI_6370_AFTER_POINT_SELECTOR_PREDICATE"
  obtain ⟨q0, _hq0, _hq0P, _hq0Fresh, _hq0Class, T, _hBadT,
      c, _hc, hBFinite, hField, hell, hxell, heI,
      _hxj, _hxGraph, _hClosed, _hOriginalBase, _hRankB,
      gB, _hCoordinates, hBFactor, _hDenominator, _hVValue, _hQ0Value, _hSurjective,
      A, hOriginalA, _hResidueIso, hAdegree,
      hFT, hEtale, points, hpJ, hAnchor, coefficients, hAux, hNonzeroJet, _hNonzeroTangent⟩ :=
    cubicThroughPointBasis_existingJointGuard_exists_sameGraph_fullDegreeAuxiliary_originalTangentSection001
      (M := M) p hp hp0 hno n y hpy j b q hRep rankPivot pairPivot a i k H hRank rho hRho
        pairCoefficients v hv hPointSelector bad hBadNonzero hFullKernel
  trace "FINAL_AI_6370_AFTER_GENUINE_AUXILIARY_SELECTOR"
  let aCol := originalGrassmannChartLineColumn001 rho T 0
  let bCol := originalGrassmannChartLineColumn001 rho T 1
  let iPivot := originalGrassmannChartLinePivot001 rho 0
  let F := cubicLinePolynomial c aCol bCol
  let B := AdjoinRoot F
  letI : Module.Finite K B := hBFinite
  letI : Field B := hField.toField
  let xB : Fin 4 → B := AdjoinRoot.root F • (fun l => algebraMap K B (aCol l)) +
    (fun l => algebraMap K B (bCol l))
  let ell : MvPolynomial (Fin 4) K := X j - C (aCol j) * X iPivot
  let r : Spec (.of B) ⟶ S := linearNormalizedPoint I xB ell hell hxell heI
  trace "FINAL_AI_6370_AFTER_LITERAL_CUT_FIELD"
  letI : Algebra.FiniteType K B := hFT
  letI : Algebra.FormallyEtale K B := hEtale
  trace "FINAL_AI_6370_AFTER_ORIGINAL_FINITE_ETALE_INSTANCES"
  let sigma := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)
  let h := sigma.comp gB
  let vv : Fin 2 → Fin 4 → M := fun r l =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun s => h (gradient s)) pairPivot l r
  let s : cubicThroughCoordinateSections p hp n y hpy := ∑ t, coefficients t • b t
  have hBBase : gB.toRingHom.comp (chartBaseMap I j) = algebraMap K B := RingHom.ext gB.commutes
  have hStrictOriginal : 3 * n.choose 2 + 1 < (hypersurfaceToBase p hp).residueDegree P.1 := by omega
  trace "FINAL_AI_6370_BEFORE_FINAL_NATIVE_ENDPOINT"
  exact False.elim (leastOriginalCubicPoint_strictWindow_actualAuxiliarySection_nonzeroNativeJet_false001
    p hp hp0 n hnThree P A hPointCoprime hleast hno hStrictOriginal hUpper hAdegree
    j gP hPBase hPMap hpy r j gB.toRingHom hBBase hBFactor hOriginalA.symm
    sigma vv hpJ hAnchor s hAux hNonzeroJet)
  trace "FINAL_AI_6370_AFTER_FINAL_EXACT"

end PfaffianDescent.Coray
