import PfaffianDescent.CorayOriginalThreeGeometricPointRankSeparationDescent
import PfaffianDescent.CorayOriginalUniformNativeRankPairPivotSpan
import PfaffianDescent.CorayOriginalProtectedPivotNativeFullJet
import PfaffianDescent.CorayOriginalNativeAuxiliaryJetResidueDerivative
import PfaffianDescent.CorayLiteralOriginalPairPolynomial

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The constructed uniform rank open and own pair pivot give rank3 in
THAT pair frame by the proved frame comparison. The actual nonzero pair
value then constructs a three-point hyperplane and descends its kernel
nonvanishing to an ORIGINAL-K through-P/A section at the SAME first point.
The protected OWN pivot constructs its native fulljet and anchor internally.
No pivot agreement, transported minor, fulljet/anchor, hyperplane or section
outcome is supplied. -/
theorem cubicThroughPointBasis_uniformRank_threeActualGeometricPoints_pairSeparation_exists_originalTangentSection001
    {K L A M : Type u} [Field K] [Field L] [CommRing A] [Field M]
    [Algebra K L] [Algebra K A] [Algebra K M]
    [Algebra.FiniteType K A] [Algebra.FormallyEtale K A] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
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
    ∀ (hA : R →ₐ[K] A) (points : Fin 3 ≃ PrimeSpectrum (M ⊗[K] A)),
    let sigma0 := originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (points 0)
    let h := sigma0.comp hA
    let z : Fin 4 → M := fun s => h (chartCoordinate (equationIdeal p hp) j s)
    let v : Fin 2 → Fin 4 → M := fun r s =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun l => h ((pderiv (j.succAbove l) p).eval₂ (algebraMap K R)
          (chartCoordinate (equationIdeal p hp) j))) pairPivot s r
    h H ≠ 0 →
    h ((pderiv (j.succAbove pairPivot) p).eval₂ (algebraMap K R)
      (chartCoordinate (equationIdeal p hp) j)) ≠ 0 →
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    ∀ ann : Fin m → M,
      (∑ t, ann t • (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v)) = 0 →
      (∑ t, ann t * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (points 1)
        (hA (e (b t)))) ≠ 0 →
    ∃ (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0)
      (hAnchor : surfacePlaneJetCoordinates z v j = 1),
    let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
    ∃ c : Fin m → K,
      let s : cubicThroughCoordinateSections p hp n y hpy := ∑ t, c t • b t
      hA (e s) = 0 ∧ gJ (e s) ≠ 0 ∧ (gJ (e s)).snd ≠ 0 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  dsimp only
  intro hA points
  let sigma0 := originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (points 0)
  let h := sigma0.comp hA
  let z : Fin 4 → M := fun s => h (chartCoordinate (equationIdeal p hp) j s)
  let v : Fin 2 → Fin 4 → M := fun r s =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun l => h ((pderiv (j.succAbove l) p).eval₂ (algebraMap K R)
        (chartCoordinate (equationIdeal p hp) j))) pairPivot s r
  intro hH hPivot ann hJet hPair
  have hBase : h.toRingHom.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M :=
    RingHom.ext h.commutes
  obtain ⟨_hpz, hpJ, hAnchor⟩ :=
    cubicOriginalChartFieldPoint_nonzeroOriginalPivot_nativeFullJet001 p hp j h.toRingHom hBase pairPivot hPivot
  refine ⟨hpJ, hAnchor, ?_⟩
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  let w : Fin m → SurfacePlaneJet M := fun t => gJ (e (b t))
  let values : Fin m → A := fun t => hA (e (b t))
  have hBaseA : hA.toRingHom.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K A :=
    RingHom.ext hA.commutes
  have hFirst (t : Fin m) : sigma0 (values t) = (w t).fst := by
    exact (cubicNormalizedFullJetChartMap_fst_eq001 p hp j h.toRingHom hBase v hpJ hAnchor
      (e (b t))).symm
  have hSection (t : Fin m) : w t =
      (q t).eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) := by
    change gJ (e (b t)) = _
    rw [cubicNormalizedFullJetChartMap_section001]
    change cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ (b t).1.1 = _
    rw [← hRep t]
    exact cubicCoordinateAlgebraEvaluation_mk p hp _ hpJ (q t)
  have hJetFamily : w = fun t =>
      (q t).eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) :=
    funext hSection
  have hSpanRank : finrank M (nativeSurfaceJetCoordinateSpan w) = 3 := by
    rw [hJetFamily]
    exact cubicThroughPointBasis_uniformNativeRank_pairPivot_finrank_three001
      p hp n y hpy j b q hRep rankPivot pairPivot a i k H hRank h hH hPivot
  have hJet' : (∑ t, ann t • w t) = 0 := by
    rw [hJetFamily]
    exact hJet
  obtain ⟨c, hValues, hNativeJet⟩ :=
    originalFiniteEtale_threeActualGeometricPoints_rankThree_pairSeparation_exists_originalCoefficients001
      points values w hFirst hSpanRank ann hJet' hPair
  let s : cubicThroughCoordinateSections p hp n y hpy := ∑ t, c t • b t
  let gJAlg : R →ₐ[K] SurfacePlaneJet M :=
    { toRingHom := gJ, commutes' := fun t => cubicNormalizedFullJetChartMap_base001 p hp j z v hpJ hAnchor t }
  have hAux : hA (e s) = 0 := by
    change hA.toLinearMap (e s) = 0
    simpa only [s, values, map_sum, map_smul, AlgHom.toLinearMap_apply] using hValues
  have hJetEq : gJ (e s) = ∑ t, c t • w t := by
    change gJAlg.toLinearMap (e s) = _
    simp only [s, map_sum, map_smul]
    rfl
  have hSectionJet : gJ (e s) ≠ 0 := by
    rw [hJetEq]
    simpa only [IsScalarTower.algebraMap_smul] using hNativeJet
  have hTangent : (gJ (e s)).snd ≠ 0 :=
    cubicThroughPointSection_throughActualAuxiliary_nonzeroNativeJet_snd_ne_zero001
      p hp n y hpy j hA.toRingHom hBaseA sigma0 v hpJ hAnchor s hAux hSectionJet
  exact ⟨c, hAux, hSectionJet, hTangent⟩

end PfaffianDescent.Coray
