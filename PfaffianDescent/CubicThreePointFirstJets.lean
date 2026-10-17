import PfaffianDescent.QuarticTangentInterpolation

/-!
Cubic interpolation on actual first-order square-zero points at three
coordinate vertices. The target includes both tangent directions of a smooth
surface, rather than a single directional dual number. These first jets are
evaluated by algebra homomorphisms, not by supplied section-space comparisons.
-/

namespace PfaffianDescent

open MvPolynomial Module TrivSqZeroExt

variable {K : Type*} [Field K]

abbrev CubicSurfaceFirstJet (K : Type*) [Field K] :=
  TrivSqZeroExt K (Fin 2 → K)

/-- A normalized projective first jet at a coordinate vertex. -/
def cubicSurfaceCoordinateJet
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (i j : Fin 4) :
    CubicSurfaceFirstJet K :=
  inl (if i = j then 1 else 0) + inr (U i j)

/-- Actual restriction of homogeneous cubics to three surface first jets. -/
noncomputable def threeCoordinateCubicFirstJetRestriction
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K]
      (Fin 3 → CubicSurfaceFirstJet K) :=
  LinearMap.pi fun i =>
    (aeval (cubicSurfaceCoordinateJet U i.castSucc)).toLinearMap.domRestrict _

theorem cubicSurfaceCoordinateJet_cube_eval
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (r i : Fin 4) :
    aeval (cubicSurfaceCoordinateJet U r) (X i ^ 3 : MvPolynomial (Fin 4) K) =
      if r = i then 1 else 0 := by
  rcases eq_or_ne r i with rfl | hr
  · apply TrivSqZeroExt.ext <;>
      simp [cubicSurfaceCoordinateJet, hdiag, pow_succ]
  · apply TrivSqZeroExt.ext <;>
      simp [cubicSurfaceCoordinateJet, hr, pow_succ]

noncomputable def cubicSurfaceCoordinateDerivativeMonomial (i j : Fin 4) :
    MvPolynomial (Fin 4) K :=
  if i = j then 0 else X i ^ 2 * X j

theorem cubicSurfaceCoordinateJet_mixed_eval
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (r i j : Fin 4) :
    aeval (cubicSurfaceCoordinateJet U r)
      (cubicSurfaceCoordinateDerivativeMonomial i j : MvPolynomial (Fin 4) K) =
      if r = i then inr (U i j) else 0 := by
  unfold cubicSurfaceCoordinateDerivativeMonomial
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  · simp only [if_neg hij]
    rcases eq_or_ne r i with rfl | hr
    · apply TrivSqZeroExt.ext <;>
        simp [cubicSurfaceCoordinateJet, hdiag, hij, pow_two]
    · apply TrivSqZeroExt.ext <;>
        simp [cubicSurfaceCoordinateJet, hr, pow_two]

/-- A cubic realizing prescribed values and two first derivatives at three
coordinate points. The coefficients b select the tangent components. -/
noncomputable def threeCoordinateCubicHermiteInterpolant
    (w : Fin 3 → CubicSurfaceFirstJet K) (b : Fin 3 → Fin 4 → K) :
    MvPolynomial (Fin 4) K :=
  ∑ i : Fin 3,
    (C (w i).fst * X i.castSucc ^ 3 +
      ∑ j : Fin 4, C (b i j) * cubicSurfaceCoordinateDerivativeMonomial i.castSucc j)

theorem threeCoordinateCubicHermiteInterpolant_homogeneous
    (w : Fin 3 → CubicSurfaceFirstJet K) (b : Fin 3 → Fin 4 → K) :
    (threeCoordinateCubicHermiteInterpolant w b).IsHomogeneous 3 := by
  apply IsHomogeneous.sum
  intro i _
  apply ((isHomogeneous_X_pow i.castSucc 3).C_mul _).add
  apply IsHomogeneous.sum
  intro j _
  unfold cubicSurfaceCoordinateDerivativeMonomial
  by_cases hij : i.castSucc = j
  · simp only [if_pos hij, mul_zero]
    exact isHomogeneous_zero (Fin 4) K 3
  · simp only [if_neg hij]
    exact (((isHomogeneous_X_pow i.castSucc 2).mul (isHomogeneous_X K j)).C_mul _)

theorem threeCoordinateCubicHermiteInterpolant_eval
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (w : Fin 3 → CubicSurfaceFirstJet K) (b : Fin 3 → Fin 4 → K)
    (hb : ∀ i, ∑ j : Fin 4, b i j • U i.castSucc j = (w i).snd)
    (r : Fin 3) :
    aeval (cubicSurfaceCoordinateJet U r.castSucc)
      (threeCoordinateCubicHermiteInterpolant w b) = w r := by
  simp only [threeCoordinateCubicHermiteInterpolant, map_sum, map_add, map_mul,
    aeval_C, cubicSurfaceCoordinateJet_cube_eval U hdiag,
    cubicSurfaceCoordinateJet_mixed_eval U hdiag,
    mul_ite, mul_zero, mul_one, Finset.sum_add_distrib]
  simp only [Fin.castSucc_inj]
  simp only [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_sum]
  · simpa [TrivSqZeroExt.snd_sum] using hb r

/-- If the coordinate directions span the actual two-dimensional tangent
target, homogeneous cubics restrict surjectively to all three first jets. -/
theorem threeCoordinateCubicFirstJetRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc))) :
    Function.Surjective (threeCoordinateCubicFirstJetRestriction U) := by
  intro w
  choose b hb using (fun i : Fin 3 => hU i (w i).snd)
  refine ⟨⟨threeCoordinateCubicHermiteInterpolant w b,
    threeCoordinateCubicHermiteInterpolant_homogeneous w b⟩, ?_⟩
  funext r
  apply threeCoordinateCubicHermiteInterpolant_eval U hdiag w b
  intro i
  simpa only [Fintype.linearCombination_apply] using hb i

/-- Three full surface jets impose exactly nine conditions on ambient
homogeneous cubics. -/
theorem threeCoordinateCubicFirstJetRestriction_ker_finrank
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc))) :
    finrank K (LinearMap.ker (threeCoordinateCubicFirstJetRestriction U)) = 11 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  have hdim := (threeCoordinateCubicFirstJetRestriction U).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (threeCoordinateCubicFirstJetRestriction_surjective U hdiag hU),
    finrank_top, four_variable_homogeneous_finrank] at hdim
  have htarget : finrank K (Fin 3 → CubicSurfaceFirstJet K) = 9 := by
    change finrank K (Fin 3 → K × (Fin 2 → K)) = 9
    simp [Module.finrank_pi_fintype, Module.finrank_prod]
  rw [htarget] at hdim
  norm_num [Nat.choose] at hdim
  omega

/-- Each interpolated first jet is an actual quotient of the polynomial
algebra, as needed to construct its projective closed immersion. -/
theorem cubicSurfaceCoordinateJet_aeval_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc))) (r : Fin 3) :
    Function.Surjective
      (aeval (cubicSurfaceCoordinateJet U r.castSucc) :
        MvPolynomial (Fin 4) K →ₐ[K] CubicSurfaceFirstJet K) := by
  intro w
  obtain ⟨q, hq⟩ :=
    threeCoordinateCubicFirstJetRestriction_surjective U hdiag hU (fun _ => w)
  exact ⟨q.val, congrFun hq r⟩

end PfaffianDescent
