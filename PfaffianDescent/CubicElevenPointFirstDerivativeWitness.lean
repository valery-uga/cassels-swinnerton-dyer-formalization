import PfaffianDescent.CubicThreePointJetWitness
import PfaffianDescent.CubicClosedPointSerreSurfaceJets
import PfaffianDescent.HomogeneousMonomialEvaluationMinor
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
An actual eleven-point cubic interpolation witness. The first three vectors
are coordinate vertices on the smooth surface. The remaining eight are
selected on the actual surface. The literal finite-product restriction is
surjective, the vectors have distinct projective directions, and the ideal
of all eleven points realizes all six surface first derivatives.
-/

namespace PfaffianDescent

open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false

theorem cubicSurfaceCoordinateJet_fst_aeval
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (i : Fin 4)
    (q : MvPolynomial (Fin 4) K) :
    (aeval (cubicSurfaceCoordinateJet U i) q).fst =
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl']
  | add q r hq hr => simp only [map_add, TrivSqZeroExt.fst_add, hq, hr]
  | mul_X q j hq =>
    rw [map_mul, TrivSqZeroExt.fst_mul, hq, map_mul, aeval_X, aeval_X]
    simp [cubicSurfaceCoordinateJet, cubicClosedPointSerreSurfaceJets_vertex]

def elevenCubicSurfacePointVectors
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    Fin 11 → Fin 4 → K :=
  fun i => Fin.addCases (m := 3) (n := 8)
    (fun i : Fin 3 => cubicClosedPointSerreSurfaceJets_vertex (K := K) i.castSucc)
    (fun i : Fin 8 => (v i).1) i

noncomputable def elevenCubicSurfaceValueRestriction
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (Fin 11 → K) :=
  homogeneousSectionRestriction (fun j i => elevenCubicSurfacePointVectors v i j) 3

theorem elevenCubicSurfaceValueRestriction_apply
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (q : homogeneousSubmodule (Fin 4) K 3) (i : Fin 11) :
    elevenCubicSurfaceValueRestriction v q i =
      aeval (elevenCubicSurfacePointVectors v i) q.1 :=
  finite_product_evaluation_apply (elevenCubicSurfacePointVectors v) q.1 i

theorem elevenCubicSurfaceValueRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    Function.Surjective (elevenCubicSurfaceValueRestriction v) := by
  intro z
  obtain ⟨q, hq⟩ := threeJetEightPointCubicValueRestriction_surjective U v hfull
    (fun i => z (i.castAdd 8), fun i => z (i.natAdd 3))
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change cubicThreeJetValueProjection (threeCoordinateCubicFirstJetRestriction U q) =
    (fun i => z (i.castAdd 8)) at hA
  change eightSurfacePointCubicRestriction v q = (fun i => z (i.natAdd 3)) at hB
  refine ⟨q, ?_⟩
  funext i
  refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
  · intro j
    have hj := congrFun hA j
    change (aeval (cubicSurfaceCoordinateJet U j.castSucc) q.1).fst = _ at hj
    rw [cubicSurfaceCoordinateJet_fst_aeval] at hj
    simpa [elevenCubicSurfaceValueRestriction_apply, elevenCubicSurfacePointVectors] using hj
  · intro j
    have hj := congrFun hB j
    change aeval (v j).1 q.1 = _ at hj
    simpa [elevenCubicSurfaceValueRestriction_apply, elevenCubicSurfacePointVectors] using hj

theorem elevenCubicSurfaceValueRestriction_ker_finrank
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hsurj : Function.Surjective (elevenCubicSurfaceValueRestriction v)) :
    finrank K (LinearMap.ker (elevenCubicSurfaceValueRestriction v)) = 9 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  have hdim := (elevenCubicSurfaceValueRestriction v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    four_variable_homogeneous_finrank, Module.finrank_pi] at hdim
  norm_num [Nat.choose] at hdim
  omega

theorem elevenCubicSurfacePointVectors_no_smul
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hsurj : Function.Surjective (elevenCubicSurfaceValueRestriction v))
    {i j : Fin 11} (hij : i ≠ j) (a : K) :
    elevenCubicSurfacePointVectors v j ≠ a • elevenCubicSurfacePointVectors v i := by
  classical
  intro hscale
  obtain ⟨q, hq⟩ := hsurj (Pi.single j 1)
  have hi : aeval (elevenCubicSurfacePointVectors v i) q.1 = 0 := by
    have h := congrFun hq i
    rw [elevenCubicSurfaceValueRestriction_apply] at h
    simpa [hij] using h
  have hj : aeval (elevenCubicSurfacePointVectors v j) q.1 = 1 := by
    have h := congrFun hq j
    rw [elevenCubicSurfaceValueRestriction_apply] at h
    simpa using h
  rw [hscale, aeval_smul_of_isHomogeneous q.1 q.2 a _, hi, mul_zero] at hj
  exact one_ne_zero hj.symm

theorem elevenCubicSurfacePointVectors_nonzero
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (i : Fin 11) : elevenCubicSurfacePointVectors v i ≠ 0 := by
  refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
  · intro j hz
    have h := congrFun hz j.castSucc
    simp [elevenCubicSurfacePointVectors, cubicClosedPointSerreSurfaceJets_vertex] at h
  · intro j
    simpa [elevenCubicSurfacePointVectors] using (v j).2.2

theorem elevenCubicSurfacePointVectors_on_surface
    (p : MvPolynomial (Fin 4) K) (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hvertices : ∀ i : Fin 3,
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i.castSucc) p = 0)
    (i : Fin 11) : aeval (elevenCubicSurfacePointVectors v i) p = 0 := by
  refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
  · intro j
    simpa [elevenCubicSurfacePointVectors] using hvertices j
  · intro j
    simpa [elevenCubicSurfacePointVectors] using (v j).2.1

noncomputable def elevenCubicSurfaceIdealFirstDerivativeRestriction
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p) :
    LinearMap.ker (elevenCubicSurfaceValueRestriction v) →ₗ[K] (Fin 3 → Fin 2 → K) :=
  (cubicThreeJetDerivativeProjection.comp (threeCoordinateCubicFirstJetRestriction U)).domRestrict _

theorem elevenCubicSurfaceIdealFirstDerivativeRestriction_surjective
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    Function.Surjective (elevenCubicSurfaceIdealFirstDerivativeRestriction U v) := by
  intro z
  obtain ⟨q, hq⟩ := hfull (fun i => TrivSqZeroExt.inr (z i), 0)
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change threeCoordinateCubicFirstJetRestriction U q =
    (fun i => TrivSqZeroExt.inr (z i)) at hA
  change eightSurfacePointCubicRestriction v q = 0 at hB
  have hzero : elevenCubicSurfaceValueRestriction v q = 0 := by
    funext i
    refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
    · intro j
      have hj := congrFun hA j
      have hf := congrArg TrivSqZeroExt.fst hj
      change (aeval (cubicSurfaceCoordinateJet U j.castSucc) q.1).fst = 0 at hf
      rw [cubicSurfaceCoordinateJet_fst_aeval] at hf
      simpa [elevenCubicSurfaceValueRestriction_apply, elevenCubicSurfacePointVectors] using hf
    · intro j
      have hj := congrFun hB j
      change aeval (v j).1 q.1 = 0 at hj
      simpa [elevenCubicSurfaceValueRestriction_apply, elevenCubicSurfacePointVectors] using hj
  refine ⟨⟨q, LinearMap.mem_ker.mpr hzero⟩, ?_⟩
  funext i
  change (threeCoordinateCubicFirstJetRestriction U q i).snd = z i
  rw [hA]
  rfl

theorem exists_eleven_cubicSurfacePoints_firstDerivative_witness
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hvertices : ∀ i : Fin 3,
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i.castSucc) p = 0) :
    ∃ (U : Fin 4 → Fin 4 → (Fin 2 → K)) (v : Fin 8 ↪ cubicSurfaceAffinePoints p),
      (∀ i, U i i = 0) ∧
      (∀ i : Fin 3, Function.Surjective (Fintype.linearCombination K (U i.castSucc))) ∧
      (∀ i : Fin 3, aeval (cubicSurfaceCoordinateJet U i.castSucc) p = 0) ∧
      Function.Surjective (elevenCubicSurfaceValueRestriction v) ∧
      Function.Surjective (elevenCubicSurfaceIdealFirstDerivativeRestriction U v) ∧
      (∀ i : Fin 11, elevenCubicSurfacePointVectors v i ≠ 0) ∧
      (∀ i : Fin 11, aeval (elevenCubicSurfacePointVectors v i) p = 0) ∧
      (∀ i j : Fin 11, i ≠ j → ∀ a : K,
        elevenCubicSurfacePointVectors v j ≠ a • elevenCubicSurfacePointVectors v i) := by
  obtain ⟨U, hdiag, hU, hpU⟩ := cubicClosedPointSerreSurfaceJets_exists_native
    p hp hp0 hvertices
  have hprime := principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  obtain ⟨v, hv⟩ := exists_eight_cubicSurfacePoints_fullFirstJet_interpolation
    U hdiag hU p hp hp0 hprime
  have hsurj := elevenCubicSurfaceValueRestriction_surjective U v hv
  exact ⟨U, v, hdiag, hU, hpU, hsurj,
    elevenCubicSurfaceIdealFirstDerivativeRestriction_surjective U v hv,
    elevenCubicSurfacePointVectors_nonzero v,
    elevenCubicSurfacePointVectors_on_surface p v hvertices,
    fun _ _ hij a => elevenCubicSurfacePointVectors_no_smul v hsurj hij a⟩

end PfaffianDescent
