import PfaffianDescent.CubicThreePointJetCompletion

/-!
An actual cubic interpolation witness with three full first jets and eight
further surface-point values. In particular the ideal of the resulting
eleven marked points maps surjectively to the six first derivatives at the
first three points. This is the polynomial witness for the Serre-fiber
evaluation argument, not yet its generic geometric transport.
-/

namespace PfaffianDescent

open MvPolynomial Module

universe u

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K]

noncomputable def eightSurfacePointCubicRestriction
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (Fin 8 → K) :=
  LinearMap.pi fun i => (MvPolynomial.aeval (v i).1).toLinearMap.domRestrict _

noncomputable def threeJetEightPointCubicRestriction
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K]
      ((Fin 3 → CubicSurfaceFirstJet K) × (Fin 8 → K)) :=
  (threeCoordinateCubicFirstJetRestriction U).prod (eightSurfacePointCubicRestriction v)

theorem threeJetEightPointCubicRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc)))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hv : Function.Surjective
      (fun q : LinearMap.ker (threeCoordinateCubicFirstJetRestriction U) =>
        fun i => MvPolynomial.aeval (v i).1 q.1.1)) :
    Function.Surjective (threeJetEightPointCubicRestriction U v) := by
  let A := threeCoordinateCubicFirstJetRestriction U
  let B := eightSurfacePointCubicRestriction v
  intro z
  obtain ⟨q, hq⟩ := threeCoordinateCubicFirstJetRestriction_surjective U hdiag hU z.1
  obtain ⟨k, hk⟩ := hv (z.2 - B q)
  refine ⟨q + k.1, ?_⟩
  apply Prod.ext
  · change A (q + k.1) = z.1
    rw [map_add, hq, LinearMap.mem_ker.mp k.2, add_zero]
  · change B (q + k.1) = z.2
    have hk' : B k.1 = z.2 - B q := hk
    rw [map_add, hk']
    abel

/-- The three full jets and eight further actual surface values can be
interpolated simultaneously by homogeneous cubics. -/
theorem exists_eight_cubicSurfacePoints_fullFirstJet_interpolation
    [IsAlgClosed K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc)))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ v : Fin 8 ↪ cubicSurfaceAffinePoints p,
      Function.Surjective (threeJetEightPointCubicRestriction U v) := by
  obtain ⟨v, hv⟩ := exists_eight_cubicSurfacePoints_firstJetKernel_evaluation_surjective
    U hdiag hU p hp hp0 hprime
  exact ⟨v, threeJetEightPointCubicRestriction_surjective U hdiag hU v hv⟩

noncomputable def cubicThreeJetValueProjection :
    (Fin 3 → CubicSurfaceFirstJet K) →ₗ[K] (Fin 3 → K) :=
  LinearMap.pi fun i =>
    (TrivSqZeroExt.fstHom K K (Fin 2 → K)).toLinearMap.comp (LinearMap.proj i)

noncomputable def cubicThreeJetDerivativeProjection :
    (Fin 3 → CubicSurfaceFirstJet K) →ₗ[K] (Fin 3 → Fin 2 → K) :=
  LinearMap.pi fun i => (TrivSqZeroExt.sndHom K (Fin 2 → K)).comp (LinearMap.proj i)

noncomputable def threeJetEightPointCubicValueRestriction
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] ((Fin 3 → K) × (Fin 8 → K)) :=
  (cubicThreeJetValueProjection.comp (threeCoordinateCubicFirstJetRestriction U)).prod
    (eightSurfacePointCubicRestriction v)

noncomputable def threeJetEightPointCubicIdealDerivativeRestriction
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    LinearMap.ker (threeJetEightPointCubicValueRestriction U v) →ₗ[K]
      (Fin 3 → Fin 2 → K) :=
  (cubicThreeJetDerivativeProjection.comp (threeCoordinateCubicFirstJetRestriction U)).domRestrict
    (LinearMap.ker (threeJetEightPointCubicValueRestriction U v))

theorem threeJetEightPointCubicValueRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    Function.Surjective (threeJetEightPointCubicValueRestriction U v) := by
  intro z
  obtain ⟨q, hq⟩ := hfull (fun i => TrivSqZeroExt.inl (z.1 i), z.2)
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change threeCoordinateCubicFirstJetRestriction U q =
    (fun i => TrivSqZeroExt.inl (z.1 i)) at hA
  change eightSurfacePointCubicRestriction v q = z.2 at hB
  refine ⟨q, ?_⟩
  apply Prod.ext
  · funext i
    change (threeCoordinateCubicFirstJetRestriction U q i).fst = z.1 i
    rw [hA]
    rfl
  · exact hB

theorem threeJetEightPointCubicValueRestriction_ker_finrank
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    finrank K (LinearMap.ker (threeJetEightPointCubicValueRestriction U v)) = 9 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  have hdim := (threeJetEightPointCubicValueRestriction U v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (threeJetEightPointCubicValueRestriction_surjective U v hfull),
    finrank_top, four_variable_homogeneous_finrank] at hdim
  have htarget : finrank K ((Fin 3 → K) × (Fin 8 → K)) = 11 := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype]
  rw [htarget] at hdim
  norm_num [Nat.choose] at hdim
  omega

theorem threeJetEightPointCubicIdealDerivativeRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    Function.Surjective (threeJetEightPointCubicIdealDerivativeRestriction U v) := by
  intro z
  obtain ⟨q, hq⟩ := hfull (fun i => TrivSqZeroExt.inr (z i), 0)
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change threeCoordinateCubicFirstJetRestriction U q =
    (fun i => TrivSqZeroExt.inr (z i)) at hA
  change eightSurfacePointCubicRestriction v q = 0 at hB
  have hzero : threeJetEightPointCubicValueRestriction U v q = 0 := by
    apply Prod.ext
    · funext i
      change (threeCoordinateCubicFirstJetRestriction U q i).fst = 0
      rw [hA]
      rfl
    · exact hB
  refine ⟨⟨q, LinearMap.mem_ker.mpr hzero⟩, ?_⟩
  funext i
  change (threeCoordinateCubicFirstJetRestriction U q i).snd = z i
  rw [hA]
  rfl

end PfaffianDescent
