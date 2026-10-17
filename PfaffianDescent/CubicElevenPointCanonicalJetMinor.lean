import PfaffianDescent.CubicNormalizedSurfaceTangentJets
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentFullInterpolation

/-!
An actual smooth cubic produces a full-jet minor using standard projective
chart coordinates and native Jacobian-pivot tangent directions.
-/

noncomputable section
namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry Module
open AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous

universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false

/-- Normalizing each marked point in its own projective chart preserves
simultaneous interpolation, with whole jet units at the first three points. -/
theorem cubicElevenPointFullJetRestriction_surjective_normalized_charts
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (anchor : Fin 11 → Fin 4)
    (hu : ∀ i, IsUnit (aeval (J i) (X (anchor (i.castAdd 8)))))
    (hx : ∀ i, x i (anchor i) ≠ 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicElevenPointFullJetRestriction
      (fun i j => (x i (anchor i))⁻¹ * x i j)
      (fun i => cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
        (X (anchor (i.castAdd 8))) (J i) (hu i))) := by
  let uj : Fin 3 → (CubicSurfaceFirstJet K)ˣ := fun i => (hu i).unit
  let uv : Fin 8 → Kˣ := fun i => Units.mk0 (x (i.natAdd 3) (anchor (i.natAdd 3))) (hx _)
  let e := cubicClosedPointSerreSurfaceJetCotangent_fullNormalizationEquiv uj uv
  intro z
  obtain ⟨q, hq⟩ := hfull (e.symm z)
  refine ⟨q, ?_⟩
  have ht : cubicElevenPointFullJetRestriction
      (fun i j => (x i (anchor i))⁻¹ * x i j)
      (fun i => cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
        (X (anchor (i.castAdd 8))) (J i) (hu i)) q =
      e (cubicElevenPointFullJetRestriction x J q) := by
    apply Prod.ext
    · funext i
      exact cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous
        (X (anchor (i.castAdd 8))) (J i) (hu i) q.1 q.2
    · funext i
      exact cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous q.1 q.2 _ _
  exact ht.trans ((congrArg e hq).trans (e.apply_symm_apply z))

/-- The witnesses are normalized on actual standard charts, and their
tangent matrices are the explicit native gradient-pivot matrices. -/
theorem exists_cubicSurfaceElevenPoint_native_canonicalJetMinor
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (anchor : Fin 11 → Fin 4)
      (pivot : Fin 3 → Fin 3) (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      (∀ i, x i (anchor i) = 1) ∧ (∀ i, aeval (x i) p = 0) ∧
      (∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) ∧
      (∀ i, aeval (x (i.castAdd 8))
        (pderiv ((anchor (i.castAdd 8)).succAbove (pivot i)) p) ≠ 0) ∧
      IsUnit (homogeneousFullJetEvaluationMinor m x (fun i =>
        cubicClosedPointSerreSurfaceJets_row (anchor (i.castAdd 8))
          (fun r => aeval (x (i.castAdd 8))
            (pderiv ((anchor (i.castAdd 8)).succAbove r) p)) (pivot i))).det := by
  classical
  obtain ⟨x, J, hx, hpx, hdir, hresidue, hpJ, hfull, _, _⟩ :=
    exists_cubicSurfaceElevenPoint_native_fullJet_witness p hp hp0
  have hcoords : ∀ i, ∃ j, x i j ≠ 0 := by
    intro i
    by_contra h
    apply hx i
    funext j
    simpa using not_exists.mp h j
  choose anchor hanchor using hcoords
  have hu : ∀ i : Fin 3, IsUnit (aeval (J i)
      (X (anchor (i.castAdd 8)) : MvPolynomial (Fin 4) K)) := by
    intro i
    apply cubicClosedPointSerreSurfaceJetCotangent_ell_jet_isUnit
    simpa only [aeval_X, hresidue] using hanchor (i.castAdd 8)
  let x' : Fin 11 → Fin 4 → K := fun i j => (x i (anchor i))⁻¹ * x i j
  let J' : Fin 3 → Fin 4 → CubicSurfaceFirstJet K := fun i =>
    cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
      (X (anchor (i.castAdd 8))) (J i) (hu i)
  have hresidue' : ∀ i j, (J' i j).fst = x' (i.castAdd 8) j := by
    intro i j
    rw [show J' i = cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
      (X (anchor (i.castAdd 8))) (J i) (hu i) by rfl,
      cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_fst]
    simp only [aeval_X, hresidue]
    rfl
  have hanchor' : ∀ i, J' i (anchor (i.castAdd 8)) = 1 := by
    intro i
    have h := cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell
      (X (anchor (i.castAdd 8))) (J i) (isHomogeneous_X K _) (hu i)
    simpa only [aeval_X] using h
  have hpJ' : ∀ i, aeval (J' i) p = 0 := by
    intro i
    exact cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_cubic
      (X (anchor (i.castAdd 8))) (J i) (hu i) p hp (hpJ i)
  have hfull' : Function.Surjective (cubicElevenPointFullJetRestriction x' J') :=
    cubicElevenPointFullJetRestriction_surjective_normalized_charts x J anchor hu hanchor hfull
  obtain ⟨pivot, m, hpivot, hm⟩ := cubicElevenPointFullJets_exists_canonical_unitMinor
    p hp hp0 x' J' (fun i => anchor (i.castAdd 8)) hresidue' hanchor' hpJ' hfull'
  refine ⟨x', anchor, pivot, m, ?_, ?_, ?_, hpivot, hm⟩
  · intro i
    exact inv_mul_cancel₀ (hanchor i)
  · intro i
    rw [show x' i = fun j => (x i (anchor i))⁻¹ * x i j by rfl,
      cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous p hp,
      hpx i, mul_zero]
  · intro i j hij a heq
    apply hdir i j hij (x j (anchor j) * a * (x i (anchor i))⁻¹)
    funext k
    have hk := congrFun heq k
    change a * ((x i (anchor i))⁻¹ * x i k) = (x j (anchor j))⁻¹ * x j k at hk
    change (x j (anchor j) * a * (x i (anchor i))⁻¹) * x i k = x j k
    calc
      _ = x j (anchor j) * (a * ((x i (anchor i))⁻¹ * x i k)) := by ring
      _ = x j (anchor j) * ((x j (anchor j))⁻¹ * x j k) := congrArg _ hk
      _ = x j k := by rw [← mul_assoc, mul_inv_cancel₀ (hanchor j), one_mul]

end PfaffianDescent
