import PfaffianDescent.CorayNativeProjectionFullJetSpanRank
import PfaffianDescent.CorayNativeSurfaceJetCoordinateSpanFrame
import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary

/-! Exact original polynomial representatives and gradients identify
native fulljet chart values with the SAME polynomial jets. An actually
proved normalized minor transfers to any other NONZERO native pivot
through the constructed tangent-frame equivalence. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The derivative evaluated through the native original-K point is
exactly the changed-coefficient derivative used by the native rows. -/
theorem originalPolynomialGradient_nativeAlgebraFieldPoint_eq001
    {K R M : Type u} [Field K] [CommRing R] [Field M]
    [Algebra K R] [Algebra K M] (h : R →ₐ[K] M)
    (x : Fin 4 → R) (p : MvPolynomial (Fin 4) K) (i : Fin 4) :
    h ((pderiv i p).eval₂ (algebraMap K R) x) =
      aeval (fun t => h (x t)) (pderiv i (p.map (algebraMap K M))) := by
  have hEval := MvPolynomial.hom_eval₂ (pderiv i p) (algebraMap K R) h.toRingHom x
  have hCoeff : h.toRingHom.comp (algebraMap K R) = algebraMap K M :=
    RingHom.ext h.commutes
  rw [hCoeff] at hEval
  have hVariables : (fun t => h.toRingHom (x t)) = (fun t => h (x t)) := by
    funext t
    rfl
  rw [hVariables] at hEval
  calc
    h ((pderiv i p).eval₂ (algebraMap K R) x) =
        h.toRingHom ((pderiv i p).eval₂ (algebraMap K R) x) := rfl
    _ = (pderiv i p).eval₂ (algebraMap K M) (fun t => h (x t)) := hEval
    _ = aeval (fun t => h (x t)) (pderiv i (p.map (algebraMap K M))) := by
      simp only [MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval,
        MvPolynomial.eval_map]

/-- The SAME homogeneous polynomial representative evaluates to the
entire native chart fulljet of the original through-point section. -/
theorem cubicNormalizedFullJetChartMap_polynomial_representative001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy) (q : MvPolynomial (Fin 4) K)
    (hRep : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) =
      q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) := by
  rw [cubicNormalizedFullJetChartMap_section001]
  change cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ s.1.1 = _
  rw [← hRep]
  exact cubicCoordinateAlgebraEvaluation_mk p hp (surfacePlaneJetCoordinates z v) hpJ q

/-- The actual native chart-jet span at one nonzero pivot equals the
literal polynomial jet span at the OTHER nonzero pivot, without an
assumed pivot equality or an externally supplied frame. -/
theorem cubicThroughPointBasis_nativeChartJetSpan_eq_polynomial_otherPivot001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z g : Fin 4 → M) (pivot pivot' : Fin 3)
    (hPivot : g (j.succAbove pivot) ≠ 0) (hPivot' : g (j.succAbove pivot') ≠ 0)
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r)) = 0)
    (hAnchor : surfacePlaneJetCoordinates z
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r) j = 1) :
    let v : Fin 2 → Fin 4 → M := fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
      j (fun t => g (j.succAbove t)) pivot i r
    let v' : Fin 2 → Fin 4 → M := fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
      j (fun t => g (j.succAbove t)) pivot' i r
    nativeSurfaceJetCoordinateSpan (fun t => cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j (b t))) =
      nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
        (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v')) := by
  have hFamily : (fun t => cubicNormalizedFullJetChartMap p hp j z
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun t => g (j.succAbove t)) pivot i r) hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j (b t))) =
      (fun t => (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
          j (fun t => g (j.succAbove t)) pivot i r))) := by
    funext t
    exact cubicNormalizedFullJetChartMap_polynomial_representative001
      p hp n y hpy j z _ hpJ hAnchor (b t) (q t) (hRep t)
  change nativeSurfaceJetCoordinateSpan (fun t => cubicNormalizedFullJetChartMap p hp j z
    (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => g (j.succAbove t)) pivot i r) hpJ hAnchor
    (cubicThroughPointChartEvaluation p hp n y hpy j (b t))) =
    nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot' i r)))
  rw [hFamily]
  exact nativeSurfaceJetCoordinateSpan_polynomialJets_eq_of_nonzeroPivots001
    j z g pivot pivot' hPivot hPivot' q

/-- The literal normalized projection minor constructs rank three for
the SAME original basis polynomials in the pair producer's potentially
DIFFERENT nonzero pivot. -/
theorem cubicThroughPointBasis_polynomial_otherPivot_finrank_three_of_nativeMinor001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z g : Fin 4 → M) (pivot pivot' : Fin 3)
    (hPivot : g (j.succAbove pivot) ≠ 0) (hPivot' : g (j.succAbove pivot') ≠ 0)
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (a i k : Fin m)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r)) = 0)
    (hAnchor : surfacePlaneJetCoordinates z
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r) j = 1)
    (hUnit : IsUnit (cubicNormalizedFullJetChartMap p hp j z
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r) hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j (b a))))
    (hMinor :
      let v : Fin 2 → Fin 4 → M := fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r
      let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      let x : Fin m → ChartRing (equationIdeal p hp) j := fun t =>
        cubicThroughPointChartEvaluation p hp n y hpy j (b t)
      let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
      let row : Fin m → Fin 2 → M := fun t =>
        (mu (nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
          (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd
      row i 0 * row k 1 - row i 1 * row k 0 ≠ 0) :
    finrank M (nativeSurfaceJetCoordinateSpan (fun t => (q t).eval₂
      (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z
        (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
          j (fun t => g (j.succAbove t)) pivot' i r)))) = 3 := by
  have hSpan := cubicThroughPointBasis_nativeChartJetSpan_eq_polynomial_otherPivot001
    p hp n y hpy j z g pivot pivot' hPivot hPivot' b q hRep hpJ hAnchor
  have hRank := nativeProjection_fulljet_coordinateSpan_finrank_three001
    (chartBaseMap (equationIdeal p hp) j)
    (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k
    (cubicNormalizedFullJetChartMap p hp j z
      (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row
        j (fun t => g (j.succAbove t)) pivot i r) hpJ hAnchor) hUnit hMinor
  rw [hSpan] at hRank
  exact hRank

end PfaffianDescent.Coray
