import PfaffianDescent.CubicFullJetTangentFrameTransport
import PfaffianDescent.CubicClosedPointSerreSurfaceJetsGradient

/-! Native Jacobian-pivot jets at arbitrary normalized smooth cubic points. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial TrivSqZeroExt Module
open AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicNormalizedSurfacePoint_coordinateOne_aeval
    (anchor : Fin 4) (x : Fin 4 → K) (hx : x anchor = 1) :
    (aeval (fun j : {j : Fin 4 // j ≠ anchor} => x j.1)).comp
      (coordinateOneEvaluation (R := K) anchor) = aeval x := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases hj : j = anchor
  · subst j
    simp [coordinateOneEvaluation, hx]
  · simp [coordinateOneEvaluation, hj, Ne.symm hj]

/-- Smoothness specializes the actual chart Jacobian unit ideal to a
nonzero retained partial at every normalized surface point. -/
theorem cubicNormalizedSurfacePoint_exists_nonzero_gradient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (anchor : Fin 4) (x : Fin 4 → K)
    (hx : x anchor = 1) (hpx : aeval x p = 0) :
    ∃ pivot : Fin 3, aeval x (pderiv (anchor.succAbove pivot) p) ≠ 0 := by
  classical
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I anchor) := (chartBaseMap I anchor).toAlgebra
  let e : MvPolynomial {j : Fin 4 // j ≠ anchor} K →ₐ[K] ChartRing I anchor :=
    aeval (fun j => chartCoordinate I anchor j.1)
  let v : MvPolynomial {j : Fin 4 // j ≠ anchor} K →ₐ[K] K :=
    aeval (fun j => x j.1)
  obtain ⟨he, hker, _⟩ :=
    smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 anchor
  have hcomp : v.comp (coordinateOneEvaluation (R := K) anchor) = aeval x :=
    cubicNormalizedSurfacePoint_coordinateOne_aeval anchor x hx
  have hv : v (coordinateOneEvaluation anchor p) = 0 := by
    rw [← AlgHom.comp_apply, hcomp]
    exact hpx
  have hle : RingHom.ker e.toRingHom ≤ RingHom.ker v.toRingHom := by
    rw [hker]
    apply Ideal.span_le.mpr
    rintro f rfl
    exact hv
  let ψ : ChartRing I anchor →ₐ[K] K := AlgHom.liftOfSurjective e he v hle
  by_contra hn
  have hall : ∀ j : {j : Fin 4 // j ≠ anchor},
      ψ (e (pderiv j (coordinateOneEvaluation anchor p))) = 0 := by
    intro j
    rw [AlgHom.liftOfSurjective_apply]
    rw [pderiv_coordinateOneEvaluation, ← AlgHom.comp_apply, hcomp]
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq j.2
    have hzero := not_exists.mp hn r
    simpa only [hr, not_not] using hzero
  have hjac : Ideal.span (Set.range (fun j : {j : Fin 4 // j ≠ anchor} =>
      e (pderiv j (coordinateOneEvaluation anchor p)))) = ⊤ :=
    smoothCubic_eliminatedChart_jacobian_top p hp hp0 anchor
  have hcontained : Ideal.span (Set.range (fun j : {j : Fin 4 // j ≠ anchor} =>
      e (pderiv j (coordinateOneEvaluation anchor p)))) ≤ RingHom.ker ψ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact hall j
  rw [hjac] at hcontained
  have hone := hcontained (show (1 : ChartRing I anchor) ∈ ⊤ from trivial)
  change ψ 1 = 0 at hone
  simpa using hone

def cubicNormalizedSurfacePoint_tangentJet
    (p : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → K) (pivot : Fin 3) : Fin 4 → CubicSurfaceFirstJet K :=
  fun j => inl (x j) + inr (cubicClosedPointSerreSurfaceJets_row anchor
    (fun r => aeval x (pderiv (anchor.succAbove r) p)) pivot j)

theorem cubicNormalizedSurfacePoint_tangentJet_cubic
    (p : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → K) (pivot : Fin 3)
    (hpx : aeval x p = 0)
    (hpivot : aeval x (pderiv (anchor.succAbove pivot) p) ≠ 0) :
    aeval (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot) p = 0 := by
  unfold cubicNormalizedSurfacePoint_tangentJet
  rw [cubicClosedPointSerreSurfaceJets_taylor, hpx]
  rw [cubicClosedPointSerreSurfaceJets_row_gradient_zero anchor
    (fun j => aeval x (pderiv j p)) pivot hpivot]
  simp

/-- Surjectivity of the actual jet algebra map forces its coordinate
directions to span the two-dimensional square-zero part. -/
theorem cubicSurfaceFirstJet_directions_surjective_of_aeval
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hJ : Function.Surjective (aeval J :
      MvPolynomial (Fin 4) K →ₐ[K] CubicSurfaceFirstJet K)) :
    Function.Surjective (Fintype.linearCombination K (fun j => (J j).snd)) := by
  intro z
  obtain ⟨q, hq⟩ := hJ (inr z)
  refine ⟨fun j => aeval (fun k => (J k).fst) (pderiv j q), ?_⟩
  funext t
  have hs := congrArg (fun z : CubicSurfaceFirstJet K => z.snd t) hq
  rw [cubicSurfaceFirstJet_snd_aeval] at hs
  simpa [Fintype.linearCombination_apply, Finset.sum_apply, smul_eq_mul] using hs

/-- The actual normalized jet is obtained from the actual Jacobian-pivot
jet by an internally constructed invertible tangent-frame map. -/
theorem cubicNormalizedSurfacePoint_exists_jetFrameMap
    (p : MvPolynomial (Fin 4) K) (anchor : Fin 4)
    (x : Fin 4 → K) (pivot : Fin 3)
    (hpivot : aeval x (pderiv (anchor.succAbove pivot) p) ≠ 0)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ j, (J j).fst = x j)
    (hanchor : J anchor = 1) (hzero : aeval J p = 0)
    (hsurj : Function.Surjective (aeval J :
      MvPolynomial (Fin 4) K →ₐ[K] CubicSurfaceFirstJet K)) :
    ∃ T : (Fin 2 → K) →ₗ[K] (Fin 2 → K), Function.Bijective T ∧
      ∀ j, J j = TrivSqZeroExt.map T
        (cubicNormalizedSurfacePoint_tangentJet p anchor x pivot j) := by
  have hv0 : (J anchor).snd = 0 := by rw [hanchor]; rfl
  have hvg : ∑ j, aeval x (pderiv j p) • (J j).snd = 0 := by
    funext t
    have h : (aeval J p).snd t = 0 := by rw [hzero]; rfl
    rw [cubicSurfaceFirstJet_snd_aeval] at h
    simpa [hresidue, Finset.sum_apply, smul_eq_mul] using h
  obtain ⟨T, hT, hrow⟩ := cubicNormalizedTangentRow_exists_frameMap anchor
    (fun j => aeval x (pderiv j p)) pivot hpivot (fun j => (J j).snd)
    hv0 hvg (cubicSurfaceFirstJet_directions_surjective_of_aeval J hsurj)
  refine ⟨T, hT, ?_⟩
  intro j
  apply TrivSqZeroExt.ext
  · simpa [cubicNormalizedSurfacePoint_tangentJet] using hresidue j
  · simpa [cubicNormalizedSurfacePoint_tangentJet] using hrow j

/-- At normalized smooth cubic points the full interpolation minor can
be chosen using the native Jacobian-pivot directions themselves. -/
theorem cubicElevenPointFullJets_exists_canonical_unitMinor
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (anchor : Fin 3 → Fin 4)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hanchor : ∀ i, J i (anchor i) = 1)
    (hpJ : ∀ i, aeval (J i) p = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    ∃ (pivot : Fin 3 → Fin 3) (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      (∀ i, aeval (x (i.castAdd 8)) (pderiv ((anchor i).succAbove (pivot i)) p) ≠ 0) ∧
      IsUnit (homogeneousFullJetEvaluationMinor m x (fun i =>
        cubicClosedPointSerreSurfaceJets_row (anchor i)
          (fun r => aeval (x (i.castAdd 8)) (pderiv ((anchor i).succAbove r) p))
          (pivot i))).det := by
  have hx : ∀ i, x (i.castAdd 8) (anchor i) = 1 := by
    intro i
    rw [← hresidue, hanchor]
    rfl
  have hpx : ∀ i : Fin 3, aeval (x (i.castAdd 8)) p = 0 := by
    intro i
    have h := congrArg TrivSqZeroExt.fst (hpJ i)
    rw [cubicSurfaceFirstJet_fst_aeval] at h
    simpa [hresidue] using h
  choose pivot hpivot using fun i : Fin 3 => cubicNormalizedSurfacePoint_exists_nonzero_gradient
    p hp hp0 (anchor i) (x (i.castAdd 8)) (hx i) (hpx i)
  choose T hT hmap using fun i => cubicNormalizedSurfacePoint_exists_jetFrameMap
    p (anchor i) (x (i.castAdd 8)) (pivot i) (hpivot i) (J i)
    (hresidue i) (hanchor i) (hpJ i)
    (cubicElevenPointFullJetRestriction_aeval_surjective x J hfull i)
  let J' : Fin 3 → Fin 4 → CubicSurfaceFirstJet K := fun i =>
    cubicNormalizedSurfacePoint_tangentJet p (anchor i) (x (i.castAdd 8)) (pivot i)
  have hfull' : Function.Surjective (cubicElevenPointFullJetRestriction x J') :=
    cubicElevenPointFullJetRestriction_surjective_of_frameMap x J J' T
      (fun i => (hT i).1) hmap hfull
  have hresidue' : ∀ i j, (J' i j).fst = x (i.castAdd 8) j := by
    intros
    simp [J', cubicNormalizedSurfacePoint_tangentJet]
  obtain ⟨m, hm⟩ := exists_unit_homogeneousFullJetEvaluationMinor_of_fullJets
    x J' hresidue' hfull'
  refine ⟨pivot, m, hpivot, ?_⟩
  simpa [J', cubicNormalizedSurfacePoint_tangentJet] using hm

end PfaffianDescent
