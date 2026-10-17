import PfaffianDescent.CorayOriginalNativeJetSpanPivotDictionary
import PfaffianDescent.CorayOriginalNativeRankSmoothGoodOpen
import PfaffianDescent.CorayLiteralOriginalPairPolynomial

/-! Bounded fieldpoint specialization of the genuinely constructed
uniform rank open into the SAME original pair-pivot fulljet span. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Exact RingHom gradient dictionary, with the actual original-K
coefficient square. No AlgHom-coordinate or dependent-jet transport. -/
private theorem uniformPairPivot_ringHom_gradient_eq001
    {K R M : Type u} [Field K] [CommRing R] [Field M] [Algebra K M]
    (c : K →+* R) (phi : R →+* M) (hCoeff : phi.comp c = algebraMap K M)
    (x : Fin 4 → R) (p : MvPolynomial (Fin 4) K) (i : Fin 4) :
    phi ((pderiv i p).eval₂ c x) =
      aeval (fun t => phi (x t)) (pderiv i (p.map (algebraMap K M))) := by
  have hEval := MvPolynomial.hom_eval₂ (pderiv i p) c phi x
  rw [hCoeff] at hEval
  calc
    phi ((pderiv i p).eval₂ c x) =
        (pderiv i p).eval₂ (algebraMap K M) (fun t => phi (x t)) := hEval
    _ = aeval (fun t => phi (x t)) (pderiv i (p.map (algebraMap K M))) := by
      simp only [MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval,
        MvPolynomial.eval_map]

/-- Bounded native-rank phase of the SAME uniform predicate. Reuse
its incoming exact coordinate/tangent binders before constructing J. -/
private theorem uniformPairPivot_ringHom_nativeRank_phase001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (pivot : Fin 3) (a i k : Fin m) (H : ChartRing (equationIdeal p hp) j)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot
      (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k H)
    (phi : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : phi.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hH : phi H ≠ 0) :
    let z : Fin 4 → M := fun t => phi (chartCoordinate (equationIdeal p hp) j t)
    let v : Fin 2 → Fin 4 → M := fun r t =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun l => aeval z (pderiv (j.succAbove l) (p.map (algebraMap K M)))) pivot t r
    (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M) z ≠ 0 ∧
    ∃ hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0,
    ∃ hAnchor : surfacePlaneJetCoordinates z v j = 1,
    let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
    finrank M (nativeSurfaceJetCoordinateSpan (fun t =>
      J (cubicThroughPointChartEvaluation p hp n y hpy j (b t)))) = 3 := by
  trace "UNIFORMPAIR_NATIVE_PHASE_ENTRY"
  intro z v
  trace "UNIFORMPAIR_NATIVE_PHASE_AFTER_EXACT_BINDERS"
  obtain ⟨hPivot, hpJ, hAnchor, hUnit, hMinor⟩ := hRank M phi hBase hH
  trace "UNIFORMPAIR_NATIVE_PHASE_AFTER_TUPLE"
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  let x : Fin m → ChartRing (equationIdeal p hp) j := fun t =>
    cubicThroughPointChartEvaluation p hp n y hpy j (b t)
  trace "UNIFORMPAIR_NATIVE_PHASE_AFTER_EXACT_J"
  have hNativeRank := nativeProjection_fulljet_coordinateSpan_finrank_three001
    (chartBaseMap (equationIdeal p hp) j) x a i k J hUnit hMinor
  trace "UNIFORMPAIR_NATIVE_PHASE_AFTER_NATIVE_RANK"
  exact ⟨hPivot, hpJ, hAnchor, hNativeRank⟩
  trace "UNIFORMPAIR_NATIVE_PHASE_AFTER_FINAL"

/-- Consume the original uniform predicate directly at its actual
RingHom fieldpoint. Keep native coordinates and the returned J unchanged
until native rank and the separate other-pivot span comparison are done. -/
private theorem uniformPairPivot_ringHom_core001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (rankPivot pairPivot : Fin 3) (a i k : Fin m)
    (H : ChartRing (equationIdeal p hp) j)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot
      (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k H)
    (phi : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : phi.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hH : phi H ≠ 0)
    (hPair : phi ((pderiv (j.succAbove pairPivot) p).eval₂
      (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j)) ≠ 0) :
    finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
      (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun s => phi (chartCoordinate (equationIdeal p hp) j s))
        (fun r s => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun l => phi ((pderiv (j.succAbove l) p).eval₂
            (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j)))
          pairPivot s r)))) = 3 := by
  trace "UNIFORMPAIR_RINGHOM_CORE_ENTRY"
  let z : Fin 4 → M := fun s => phi (chartCoordinate (equationIdeal p hp) j s)
  let g : Fin 4 → M := fun s => aeval z (pderiv s (p.map (algebraMap K M)))
  let gamma : Fin 3 → M := fun l => phi ((pderiv (j.succAbove l) p).eval₂
    (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j))
  have hGradient (l : Fin 3) : gamma l = g (j.succAbove l) :=
    uniformPairPivot_ringHom_gradient_eq001 (chartBaseMap (equationIdeal p hp) j)
      phi hBase (chartCoordinate (equationIdeal p hp) j) p (j.succAbove l)
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_GRADIENT"
  obtain ⟨hRankPivot, hpJ, hAnchor, hNativeRank⟩ :=
    uniformPairPivot_ringHom_nativeRank_phase001 p hp n y hpy j b rankPivot a i k H
      hRank phi hBase hH
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_NATIVE_RANK_PHASE"
  have hRankPivot' : g (j.succAbove rankPivot) ≠ 0 := by
    simpa only [g, MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval,
      MvPolynomial.eval_map] using hRankPivot
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_RANK_PIVOT"
  have hPairPivot' : g (j.succAbove pairPivot) ≠ 0 :=
    fun hz => hPair ((hGradient pairPivot).trans hz)
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_PAIR_PIVOT"
  trace "UNIFORMPAIR_RINGHOM_CORE_BEFORE_SPAN_EQUALITY"
  have hSpan := cubicThroughPointBasis_nativeChartJetSpan_eq_polynomial_otherPivot001
    p hp n y hpy j z g rankPivot pairPivot hRankPivot' hPairPivot' b q hRep hpJ hAnchor
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_SPAN_EQUALITY"
  have hNativeRank' :
      finrank M (nativeSurfaceJetCoordinateSpan (fun t =>
        cubicNormalizedFullJetChartMap p hp j z
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun l => g (j.succAbove l)) rankPivot l r) hpJ hAnchor
          (cubicThroughPointChartEvaluation p hp n y hpy j (b t)))) = 3 := hNativeRank
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_EXPLICIT_RANK_TYPE"
  rw [hSpan] at hNativeRank'
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_SPAN_TRANSPORT"
  have hGradientFunction : (fun l => g (j.succAbove l)) = gamma := by
    funext l
    exact (hGradient l).symm
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_GRADIENT_FUNCTION"
  have hRankTransport :
      finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun l => g (j.succAbove l)) pairPivot l r)))) =
      finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            gamma pairPivot l r)))) :=
    congrArg (fun gradient : Fin 3 → M =>
      finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            gradient pairPivot l r))))) hGradientFunction
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_RANK_CONGRUENCE"
  have hConvertedRank :
      finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            gamma pairPivot l r)))) = 3 :=
    hRankTransport.symm.trans hNativeRank'
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_CONVERTED_RANK"
  exact hConvertedRank
  trace "UNIFORMPAIR_RINGHOM_CORE_AFTER_FINAL"

/-- The actual uniform native rank producer supplies the nonzero rank
pivot and normalized minor at this SAME original-K fieldpoint. The own
pair pivot is protected by the constructed joint principal open. Their
frame equality gives actual rank3 of the SAME original basis polynomial
jet span without a pivot-agreement or separate rank/minor certificate. -/
theorem cubicThroughPointBasis_uniformNativeRank_pairPivot_finrank_three001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (rankPivot pairPivot : Fin 3) (a i k : Fin m)
    (H : ChartRing (equationIdeal p hp) j)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot
      (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k H) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ h : R →ₐ[K] M, h H ≠ 0 →
      h ((pderiv (j.succAbove pairPivot) p).eval₂ (algebraMap K R)
        (chartCoordinate (equationIdeal p hp) j)) ≠ 0 →
      finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates (fun s => h (chartCoordinate (equationIdeal p hp) j s))
          (fun r s => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun l => h ((pderiv (j.succAbove l) p).eval₂ (algebraMap K R)
              (chartCoordinate (equationIdeal p hp) j))) pairPivot s r)))) = 3 := by
  trace "UNIFORMPAIR_DIRECT_ENTRY"
  intro R h hH hPairPivot
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  have hBase : h.toRingHom.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M :=
    RingHom.ext h.commutes
  have hPairEvaluation :
      h.toRingHom ((pderiv (j.succAbove pairPivot) p).eval₂
        (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j)) =
      h ((pderiv (j.succAbove pairPivot) p).eval₂
        (algebraMap K R) (chartCoordinate (equationIdeal p hp) j)) := rfl
  have hPairRingHom : h.toRingHom ((pderiv (j.succAbove pairPivot) p).eval₂
      (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j)) ≠ 0 :=
    fun hz => hPairPivot (hPairEvaluation.symm.trans hz)
  trace "UNIFORMPAIR_DIRECT_AFTER_POINT_SQUARE"
  have hCore := uniformPairPivot_ringHom_core001 p hp n y hpy j b q hRep
    rankPivot pairPivot a i k H hRank h.toRingHom hBase hH hPairRingHom
  trace "UNIFORMPAIR_DIRECT_AFTER_CORE"
  have hCoordinates :
      (fun s : Fin 4 => h.toRingHom (chartCoordinate (equationIdeal p hp) j s)) =
      (fun s : Fin 4 => h (chartCoordinate (equationIdeal p hp) j s)) := by
    funext s
    rfl
  have hGradients :
      (fun l : Fin 3 => h.toRingHom ((pderiv (j.succAbove l) p).eval₂
        (chartBaseMap (equationIdeal p hp) j) (chartCoordinate (equationIdeal p hp) j))) =
      (fun l : Fin 3 => h ((pderiv (j.succAbove l) p).eval₂
        (algebraMap K R) (chartCoordinate (equationIdeal p hp) j))) := by
    funext l
    rfl
  rw [hCoordinates, hGradients] at hCore
  exact hCore
  trace "UNIFORMPAIR_DIRECT_AFTER_FINAL"

end PfaffianDescent.Coray
