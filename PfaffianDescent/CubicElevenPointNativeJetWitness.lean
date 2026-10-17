import PfaffianDescent.CubicElevenPointFirstDerivativeWitness
import PfaffianDescent.CubicClosedPointSerreSurfaceCoordinates
import PfaffianDescent.VoisinLinearChangeEvaluation

/-!
Eleven actual points and three actual full square-zero jets on an arbitrary
smooth cubic over an algebraically closed field. All coordinate choices and
the simultaneous interpolation witness are constructed internally.
-/

namespace PfaffianDescent

open MvPolynomial Module AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false

noncomputable def cubicElevenPointValueRestriction (x : Fin 11 → Fin 4 → K) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (Fin 11 → K) :=
  homogeneousSectionRestriction (fun j i => x i j) 3

noncomputable def cubicElevenPointFullJetRestriction
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K]
      ((Fin 3 → CubicSurfaceFirstJet K) × (Fin 8 → K)) :=
  (LinearMap.pi fun i => (aeval (J i)).toLinearMap.domRestrict _).prod
    (LinearMap.pi fun i => (aeval (x (i.natAdd 3))).toLinearMap.domRestrict _)

noncomputable def cubicElevenPointIdealFirstDerivativeRestriction
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) :
    LinearMap.ker (cubicElevenPointValueRestriction x) →ₗ[K] (Fin 3 → Fin 2 → K) :=
  (LinearMap.pi fun i => (TrivSqZeroExt.sndHom K (Fin 2 → K)).comp
    ((aeval (J i)).toLinearMap.domRestrict _)).domRestrict _

theorem cubicSurfaceFirstJet_fst_aeval
    (J : Fin 4 → CubicSurfaceFirstJet K) (q : MvPolynomial (Fin 4) K) :
    (aeval J q).fst = aeval (fun j => (J j).fst) q := by
  have h : (TrivSqZeroExt.fstHom K K (Fin 2 → K)).comp (aeval J) =
      aeval (fun j => (J j).fst) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact DFunLike.congr_fun h q

theorem cubicElevenPointValueRestriction_surjective_of_fullJets
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicElevenPointValueRestriction x) := by
  intro z
  obtain ⟨q, hq⟩ := hfull
    (fun i => TrivSqZeroExt.inl (z (i.castAdd 8)), fun i => z (i.natAdd 3))
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change (fun i => aeval (J i) q.1) =
    (fun i => TrivSqZeroExt.inl (z (i.castAdd 8))) at hA
  change (fun i : Fin 8 => aeval (x (i.natAdd 3)) q.1) =
    (fun i : Fin 8 => z (i.natAdd 3)) at hB
  refine ⟨q, ?_⟩
  funext i
  refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
  · intro j
    have h := congrArg TrivSqZeroExt.fst (congrFun hA j)
    rw [cubicSurfaceFirstJet_fst_aeval] at h
    simpa [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply, hresidue] using h
  · intro j
    simpa [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using congrFun hB j

theorem cubicElevenPointIdealFirstDerivativeRestriction_surjective_of_fullJets
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicElevenPointIdealFirstDerivativeRestriction x J) := by
  intro z
  obtain ⟨q, hq⟩ := hfull (fun i => TrivSqZeroExt.inr (z i), 0)
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change (fun i => aeval (J i) q.1) = (fun i => TrivSqZeroExt.inr (z i)) at hA
  change (fun i : Fin 8 => aeval (x (i.natAdd 3)) q.1) = 0 at hB
  have hzero : cubicElevenPointValueRestriction x q = 0 := by
    funext i
    refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
    · intro j
      have h := congrArg TrivSqZeroExt.fst (congrFun hA j)
      rw [cubicSurfaceFirstJet_fst_aeval] at h
      simpa [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply, hresidue] using h
    · intro j
      simpa [cubicElevenPointValueRestriction, homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply] using congrFun hB j
  refine ⟨⟨q, LinearMap.mem_ker.mpr hzero⟩, ?_⟩
  funext i
  change (aeval (J i) q.1).snd = z i
  rw [show aeval (J i) q.1 = TrivSqZeroExt.inr (z i) from congrFun hA i]
  rfl

/-- Each selected first jet is an actual quotient of the polynomial algebra;
full simultaneous homogeneous interpolation supplies the preimages. -/
theorem cubicElevenPointFullJetRestriction_aeval_surjective
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J))
    (i : Fin 3) : Function.Surjective (aeval (J i) :
      MvPolynomial (Fin 4) K →ₐ[K] CubicSurfaceFirstJet K) := by
  classical
  intro z
  let w : Fin 3 → CubicSurfaceFirstJet K := Pi.single i z
  obtain ⟨q, hq⟩ := hfull (w, 0)
  have h := congrFun (congrArg Prod.fst hq) i
  change aeval (J i) q.1 = w i at h
  exact ⟨q.1, by simpa [w] using h⟩

theorem cubicElevenPointFullJetRestriction_linearChange_surjective
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    {p : MvPolynomial (Fin 4) K} (v : Fin 8 → cubicSurfaceAffinePoints p)
    (hfull : Function.Surjective (threeJetEightPointCubicRestriction U v)) :
    Function.Surjective (cubicElevenPointFullJetRestriction
      (fun i => M.mulVec (elevenCubicSurfacePointVectors v i))
      (fun i => (M.map (algebraMap K (CubicSurfaceFirstJet K))).mulVec
        (cubicSurfaceCoordinateJet U i.castSucc))) := by
  intro z
  obtain ⟨q, hq⟩ := hfull z
  let q' : homogeneousSubmodule (Fin 4) K 3 :=
    ⟨linearSubstitution M⁻¹ q.1, linearSubstitution_homogeneous M⁻¹ q.2⟩
  have hqq : linearSubstitution M q'.1 = q.1 := by
    change ((linearSubstitution M).comp (linearSubstitution M⁻¹)) q.1 = q.1
    rw [linearSubstitution_comp, Matrix.nonsing_inv_mul M hM, linearSubstitution_one]
    rfl
  refine ⟨q', ?_⟩
  apply Prod.ext
  · funext i
    have h := congrFun (congrArg Prod.fst hq) i
    change aeval (cubicSurfaceCoordinateJet U i.castSucc) q.1 = z.1 i at h
    change aeval ((M.map (algebraMap K (CubicSurfaceFirstJet K))).mulVec
      (cubicSurfaceCoordinateJet U i.castSucc)) q'.1 = z.1 i
    rw [← linearSubstitution_aeval, hqq]
    exact h
  · funext i
    have h := congrFun (congrArg Prod.snd hq) i
    change aeval (v i).1 q.1 = z.2 i at h
    change aeval (M.mulVec (elevenCubicSurfacePointVectors v (i.natAdd 3)))
      (linearSubstitution M⁻¹ q.1) = z.2 i
    rw [linearSubstitution_eval, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
    simpa [elevenCubicSurfacePointVectors] using h

theorem cubicSurfaceCoordinateJet_linearChange_fst
    (M : Matrix (Fin 4) (Fin 4) K)
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (i j : Fin 4) :
    ((M.map (algebraMap K (CubicSurfaceFirstJet K))).mulVec
      (cubicSurfaceCoordinateJet U i) j).fst =
      M.mulVec (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) j := by
  classical
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum,
    TrivSqZeroExt.algebraMap_eq_inl',
    cubicSurfaceCoordinateJet, cubicClosedPointSerreSurfaceJets_vertex]

/-- On the original cubic, eleven actual nonzero projectively distinct points
and three full surface jets realize arbitrary first jets and remaining eight
values. Their literal eleven-point ideal realizes all six derivatives. -/
theorem exists_cubicSurfaceElevenPoint_native_fullJet_witness
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K),
      (∀ i, x i ≠ 0) ∧ (∀ i, aeval (x i) p = 0) ∧
      (∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) ∧
      (∀ i j, (J i j).fst = x (i.castAdd 8) j) ∧
      (∀ i, aeval (J i) p = 0) ∧
      Function.Surjective (cubicElevenPointFullJetRestriction x J) ∧
      Function.Surjective (cubicElevenPointValueRestriction x) ∧
      Function.Surjective (cubicElevenPointIdealFirstDerivativeRestriction x J) := by
  classical
  obtain ⟨w, hM, _, _, _, hp', hp0', hsmooth, hprime, hvertices⟩ :=
    cubicClosedPointSerreSurfaceCoordinates_exists_native p hp hp0
  let M : Matrix (Fin 4) (Fin 4) K := Matrix.of (fun r j => (w j).1 r)
  let p' := linearSubstitution M p
  letI : Smooth (hypersurfaceToBase p' (linearSubstitution_homogeneous M hp)) := hsmooth
  obtain ⟨U, hdiag, hU, hpU⟩ := cubicClosedPointSerreSurfaceJets_exists_native
    p' (linearSubstitution_homogeneous M hp) hp0' (fun i => hvertices i.castSucc)
  obtain ⟨v, hv⟩ := exists_eight_cubicSurfacePoints_fullFirstJet_interpolation
    U hdiag hU p' (linearSubstitution_homogeneous M hp) hp0' hprime
  let y := elevenCubicSurfacePointVectors v
  let x : Fin 11 → Fin 4 → K := fun i => M.mulVec (y i)
  let J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K := fun i =>
    (M.map (algebraMap K (CubicSurfaceFirstJet K))).mulVec
      (cubicSurfaceCoordinateJet U i.castSucc)
  have hy0 : ∀ i, y i ≠ 0 := elevenCubicSurfacePointVectors_nonzero v
  have hys : ∀ i, aeval (y i) p' = 0 :=
    elevenCubicSurfacePointVectors_on_surface p' v (fun i => hvertices i.castSucc)
  have hvsurj := elevenCubicSurfaceValueRestriction_surjective U v hv
  have hymul : ∀ i j, i ≠ j → ∀ a : K, a • y i ≠ y j := by
    intro i j hij a
    exact (elevenCubicSurfacePointVectors_no_smul v hvsurj hij a).symm
  have hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j := by
    intro i j
    simpa [J, x, y, elevenCubicSurfacePointVectors] using
      cubicSurfaceCoordinateJet_linearChange_fst M U i.castSucc j
  have hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J) :=
    cubicElevenPointFullJetRestriction_linearChange_surjective M hM U v hv
  refine ⟨x, J, linearChange_points_nonzero M ((Matrix.isUnit_iff_isUnit_det M).mpr hM)
    y hy0, ?_,
    linearChange_points_projectivelyDistinct M ((Matrix.isUnit_iff_isUnit_det M).mpr hM)
      y hymul, hresidue, ?_, hfull,
    cubicElevenPointValueRestriction_surjective_of_fullJets x J hresidue hfull,
    cubicElevenPointIdealFirstDerivativeRestriction_surjective_of_fullJets x J hresidue hfull⟩
  · intro i
    change aeval (M.mulVec (y i)) p = 0
    rw [← linearSubstitution_eval]
    exact hys i
  · intro i
    change aeval ((M.map (algebraMap K (CubicSurfaceFirstJet K))).mulVec
      (cubicSurfaceCoordinateJet U i.castSucc)) p = 0
    rw [← linearSubstitution_aeval]
    exact hpU i

end PfaffianDescent
