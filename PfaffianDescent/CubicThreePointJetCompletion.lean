import PfaffianDescent.CubicThreePointFirstJets
import PfaffianDescent.CubicSurfacePointEvaluation

/-!
Eight further actual points can impose independent cubic conditions while
three prescribed surface first jets remain zero. The first-jet kernel has
dimension eleven; the only possible equation vanishing everywhere on the
prime cubic surface is its defining cubic, leaving at least ten independent
functions on the actual surface. The eight points are selected internally.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

noncomputable def cubicThreeJetKernelSurfaceEvaluation
    {K : Type u} [Field K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    LinearMap.ker (threeCoordinateCubicFirstJetRestriction U) →ₗ[K]
      (cubicSurfaceAffinePoints p → K) :=
  (cubicSurfaceCoordinatePointEvaluation p hp (d := 3)).comp
    ((cubicSurfaceHomogeneousCoordinateProjection p hp 3).domRestrict
      (LinearMap.ker (threeCoordinateCubicFirstJetRestriction U)))

theorem cubicThreeJetKernelSurfaceEvaluation_apply
    {K : Type u} [Field K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : LinearMap.ker (threeCoordinateCubicFirstJetRestriction U))
    (x : cubicSurfaceAffinePoints p) :
    cubicThreeJetKernelSurfaceEvaluation U p hp q x =
      MvPolynomial.aeval x.1 q.1.1 := rfl

theorem cubicThreeJetKernelSurfaceEvaluation_ker_finrank_le_one
    {K : Type u} [Field K] [IsAlgClosed K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    finrank K (LinearMap.ker (cubicThreeJetKernelSurfaceEvaluation U p hp)) ≤ 1 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  let f := cubicThreeJetKernelSurfaceEvaluation U p hp
  let P := cubicSurfaceProjection p hp 3
  have hmem (q : LinearMap.ker f) : q.1.1 ∈ LinearMap.ker P := by
    have hzero : cubicSurfaceHomogeneousCoordinateProjection p hp 3 q.1.1 = 0 := by
      apply cubicSurfaceCoordinatePointEvaluation_injective p hp (by decide) hprime
      change f q.1 = 0
      exact LinearMap.mem_ker.mp q.2
    change P q.1.1 = 0
    exact congrArg Subtype.val hzero
  let g : LinearMap.ker f →ₗ[K] LinearMap.ker P :=
    { toFun := fun q => ⟨q.1.1, hmem q⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hg : Function.Injective g := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker P => z.1) hqr
  have hdim : finrank K (LinearMap.ker P) = 1 := by
    change finrank K (LinearMap.ker (cubicSurfaceProjection p hp (0 + 3))) = 1
    rw [← cubicSurfaceRelation_range_eq_projection_ker p hp hp0 0,
      LinearMap.finrank_range_of_inj (cubicSurfaceRelation_injective p hp hp0 0),
      four_variable_homogeneous_finrank]
    decide
  exact hdim ▸ LinearMap.finrank_le_finrank_of_injective hg

theorem cubicThreeJetKernelSurfaceEvaluation_range_finrank_ge_ten
    {K : Type u} [Field K] [IsAlgClosed K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc)))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    10 ≤ finrank K (LinearMap.range (cubicThreeJetKernelSurfaceEvaluation U p hp)) := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  have hdim := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := LinearMap.ker (threeCoordinateCubicFirstJetRestriction U))
    (V₂ := cubicSurfaceAffinePoints p → K)
    (cubicThreeJetKernelSurfaceEvaluation U p hp)
  rw [threeCoordinateCubicFirstJetRestriction_ker_finrank U hdiag hU] at hdim
  have hker := cubicThreeJetKernelSurfaceEvaluation_ker_finrank_le_one U p hp hp0 hprime
  omega

/-- Eight actual cubic-surface points impose independent conditions on
cubics whose full first jets vanish at the three coordinate vertices. -/
theorem exists_eight_cubicSurfacePoints_firstJetKernel_evaluation_surjective
    {K : Type u} [Field K] [IsAlgClosed K]
    (U : Fin 4 → Fin 4 → (Fin 2 → K)) (hdiag : ∀ i, U i i = 0)
    (hU : ∀ i : Fin 3, Function.Surjective
      (Fintype.linearCombination K (U i.castSucc)))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ v : Fin 8 ↪ cubicSurfaceAffinePoints p,
      Function.Surjective
        (fun q : LinearMap.ker (threeCoordinateCubicFirstJetRestriction U) =>
          fun i => MvPolynomial.aeval (v i).1 q.1.1) := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 4) K 3)
  let f := cubicThreeJetKernelSurfaceEvaluation U p hp
  let W := LinearMap.range f
  have hdim : 8 ≤ finrank K W := by
    change 8 ≤ finrank K (LinearMap.range (cubicThreeJetKernelSurfaceEvaluation U p hp))
    have hten := cubicThreeJetKernelSurfaceEvaluation_range_finrank_ge_ten
      U hdiag hU p hp hp0 hprime
    omega
  obtain ⟨v, hv⟩ := exists_embedding_evaluation_surjective W.subtype
    W.subtype_injective 8 hdim
  refine ⟨v, ?_⟩
  intro z
  obtain ⟨w, hw⟩ := hv z
  obtain ⟨q, hq⟩ := w.2
  refine ⟨q, ?_⟩
  funext i
  have hi := congrFun hw i
  change w.1 (v i) = z i at hi
  rw [← hq] at hi
  exact hi

end PfaffianDescent
