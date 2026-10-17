import PfaffianDescent.CorayOriginalNativeMinorSpecializationHelpers
import PfaffianDescent.CorayOriginalNormalizedMinorClearingHelpers

/-! The literal original minor numerator specializes to a nonzero minor
of the entire normalized native fulljet, at every original chart field
point where its pivot/denominator/numerator product is nonzero. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal original principal-open condition derives the complete
native normalized fulljet relation, denominator unit and nonzero minor
at every actual chart fieldpoint. The actually nonzero original pivot
gradient is retained for comparing independently constructed frames.
No desired tangent rank is supplied. -/
theorem cubicChartPolynomialFamily_nativeNormalizedMinor_of_originalNumerator_nonzero001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) (pivot : Fin 3)
    {m : ℕ} (x : Fin m → ChartRing (equationIdeal p hp) j)
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hrep : ∀ t, (q t).eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j) = x t) (a i k : Fin m)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M) :
    let I := equationIdeal p hp
    let grad : Fin 3 → ChartRing I j := fun t =>
      (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
    let N : Fin m → Fin 2 → ChartRing I j := fun t r =>
      grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q t)).eval₂
        (chartBaseMap I j) (chartCoordinate I j) -
      grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q t)).eval₂
        (chartBaseMap I j) (chartCoordinate I j)
    let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
    g (grad pivot * x a * D) ≠ 0 →
    let z : Fin 4 → M := fun t => g (chartCoordinate I j t)
    let v : Fin 2 → Fin 4 → M := fun r t =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
        (fun s => aeval z (pderiv (j.succAbove s) (p.map (algebraMap K M)))) pivot t r
    (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M) z ≠ 0 ∧
    ∃ hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0,
    ∃ hAnchor : surfacePlaneJetCoordinates z v j = 1,
    let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
    ∃ hUnit : IsUnit (J (x a)),
    let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
    let row : Fin m → Fin 2 → M := fun t =>
      (mu (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd
    row i 0 * row k 1 - row i 1 * row k 0 ≠ 0 := by
  let I := equationIdeal p hp
  let grad : Fin 3 → ChartRing I j := fun t =>
    (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
  let N : Fin m → Fin 2 → ChartRing I j := fun t r =>
    grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j) -
    grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j)
  let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
  change g (grad pivot * x a * D) ≠ 0 → _
  intro hH
  have hProduct : g (grad pivot) * g (x a) * g D ≠ 0 := by
    simpa only [map_mul] using hH
  have hD : g D ≠ 0 := (mul_ne_zero_iff.mp hProduct).2
  have hGa : g (grad pivot) * g (x a) ≠ 0 := (mul_ne_zero_iff.mp hProduct).1
  have hG : g (grad pivot) ≠ 0 := (mul_ne_zero_iff.mp hGa).1
  have ha : g (x a) ≠ 0 := (mul_ne_zero_iff.mp hGa).2
  let z : Fin 4 → M := fun t => g (chartCoordinate I j t)
  let v : Fin 2 → Fin 4 → M := fun r t =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun s => aeval z (pderiv (j.succAbove s) (p.map (algebraMap K M)))) pivot t r
  have hPivot : (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M) z ≠ 0 := by
    have h := MvPolynomial.hom_eval₂ (pderiv (j.succAbove pivot) p)
      (chartBaseMap I j) g (chartCoordinate I j)
    rw [hBase] at h
    rwa [h] at hG
  obtain ⟨hpJ, hAnchor⟩ := cubicChartFieldPoint_pivotFullJet_relation_anchor001 p hp j g hBase pivot hPivot
  let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  have hfst : ∀ t, (J t).fst = g t :=
    cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor
  let hUnit : IsUnit (J (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (by rw [hfst]; exact isUnit_iff_ne_zero.mpr ha)
  let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
  have hN (t : Fin m) (r : Fin 2) : (J (x t)).snd r = g (N t r) / g (grad pivot) := by
    rw [← hrep t]
    exact cubicNormalizedFullJetChartMap_polynomialDirection_eq_cleared001
      p hp j g hBase pivot hPivot hpJ hAnchor (q t) r
  have hrow (t : Fin m) (r : Fin 2) :
      (mu (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd r =
      g (N t r * x a - x t * N a r) / (g (grad pivot) * g (x a) ^ 2) := by
    rw [nativeLocalizedProjectiveChartMap_fulljet_row_eq_quotientRule001
      (chartBaseMap I j) x a g J hfst ha t r]
    rw [hN t r, hN a r]
    simp only [map_sub, map_mul]
    field_simp [hG, ha]
    <;> ring
  refine ⟨hPivot, hpJ, hAnchor, hUnit, ?_⟩
  change (mu _).snd 0 * (mu _).snd 1 - (mu _).snd 1 * (mu _).snd 0 ≠ 0
  rw [hrow i 0, hrow k 1, hrow i 1, hrow k 0,
    div_mul_div_comm, div_mul_div_comm, ← sub_div]
  have hNum :
      g (N i 0 * x a - x i * N a 0) * g (N k 1 * x a - x k * N a 1) -
        g (N i 1 * x a - x i * N a 1) * g (N k 0 * x a - x k * N a 0) = g D := by
    simp only [D, normalizedProjectionMinorNumerator, map_sub, map_mul]
  rw [hNum]
  exact div_ne_zero hD (mul_ne_zero
    (mul_ne_zero hG (pow_ne_zero 2 ha)) (mul_ne_zero hG (pow_ne_zero 2 ha)))

end PfaffianDescent.Coray
end
