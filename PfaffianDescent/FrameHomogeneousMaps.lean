import PfaffianDescent.FrameComplex
import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.FrameHilbertFunction

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators

abbrev FrameHomogeneous (K : Type*) [Field K] (d : ℕ) :=
  homogeneousSubmodule (Fin 4) K d

section
variable {K : Type*} [Field K]

lemma frameRelations_homogeneous (i : Fin 5) :
    (frameRelations (K := K) i).IsHomogeneous 2 := by
  fin_cases i <;> exact ((isHomogeneous_X K _).mul (isHomogeneous_X K _)).sub
    ((isHomogeneous_X K _).mul (isHomogeneous_X K _))

lemma frameMatrix_homogeneous (i j : Fin 5) :
    (frameMatrix (X : Fin 4 → MvPolynomial (Fin 4) K) i j).IsHomogeneous 1 := by
  fin_cases i <;> fin_cases j
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (-X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4)).neg
  · change (-X 3 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (3 : Fin 4)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4))
  · change (-(-X 1) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4)).neg.neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (X 2 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (2 : Fin 4))
  · change (-X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4)).neg
  · change (-(-X 3) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (3 : Fin 4)).neg.neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4))
  · change (-X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (-X 2 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (2 : Fin 4)).neg
  · change (-X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem
  · change (X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4))
  · change (-X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4)).neg
  · change (-(-X 1) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (1 : Fin 4)).neg.neg
  · change (-(-X 0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4)).neg.neg
  · change (-X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (isHomogeneous_X K (0 : Fin 4)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (FrameHomogeneous K 1).zero_mem

noncomputable def frameVectorInclusion (d : ℕ) :
    (Fin 5 → FrameHomogeneous K d) →ₗ[K] (Fin 5 → MvPolynomial (Fin 4) K) where
  toFun v i := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma frameVectorInclusion_injective (d : ℕ) :
    Function.Injective (frameVectorInclusion (K := K) d) := by
  intro v w h
  funext i
  exact Subtype.ext (congrFun h i)

lemma frameLastMap_homogeneous (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    (frameLastMap (frameVectorInclusion d v)).IsHomogeneous (d+2) := by
  change (∑ i, (v i).val * frameRelations i) ∈ FrameHomogeneous K (d+2)
  exact Submodule.sum_mem _ fun i _ => (v i).property.mul (frameRelations_homogeneous i)

lemma frameMiddleMap_homogeneous (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) (i : Fin 5) :
    (frameMiddleMap (frameVectorInclusion d v) i).IsHomogeneous (d+1) := by
  change (∑ j, frameMatrix X i j * (v j).val) ∈ FrameHomogeneous K (d+1)
  apply Submodule.sum_mem
  intro j _
  change (frameMatrix X i j * (v j).val).IsHomogeneous (d+1)
  have h := (frameMatrix_homogeneous (K := K) i j).mul (v j).property
  rwa [Nat.add_comm 1 d] at h

noncomputable def frameGradedLast (d : ℕ) :
    (Fin 5 → FrameHomogeneous K d) →ₗ[K] FrameHomogeneous K (d+2) :=
  (((frameLastMap (K := K)).restrictScalars K).comp (frameVectorInclusion d)).codRestrict _
    (frameLastMap_homogeneous d)

noncomputable def frameGradedMiddle (d : ℕ) :
    (Fin 5 → FrameHomogeneous K d) →ₗ[K] (Fin 5 → FrameHomogeneous K (d+1)) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp ((frameMiddleMap (K := K)).restrictScalars K)).comp
      (frameVectorInclusion d)).codRestrict _ (fun v => frameMiddleMap_homogeneous d v i)

noncomputable def frameGradedFirst (d : ℕ) :
    FrameHomogeneous K d →ₗ[K] (Fin 5 → FrameHomogeneous K (d+2)) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp ((frameFirstMap (K := K)).restrictScalars K)).comp
      (FrameHomogeneous K d).subtype).codRestrict _
      (fun r => r.property.mul (frameRelations_homogeneous i))

@[simp] lemma frameGradedLast_val (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    (frameGradedLast d v).val = frameLastMap (frameVectorInclusion d v) := rfl

@[simp] lemma frameGradedMiddle_val (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    frameVectorInclusion (d+1) (frameGradedMiddle d v) =
      frameMiddleMap (frameVectorInclusion d v) := rfl

@[simp] lemma frameGradedFirst_val (d : ℕ) (r : FrameHomogeneous K d) :
    frameVectorInclusion (d+2) (frameGradedFirst d r) = frameFirstMap r.val := rfl

lemma frameGradedMiddle_range_le (d : ℕ) :
    LinearMap.range (frameGradedMiddle (K := K) d) ≤ LinearMap.ker (frameGradedLast (d+1)) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  rw [frameGradedLast_val, frameGradedMiddle_val]
  have h := LinearMap.congr_fun (frameLastMap_comp_middle (K := K))
    (frameVectorInclusion d v)
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_zero] using h

lemma frameGradedFirst_injective (d : ℕ) :
    Function.Injective (frameGradedFirst (K := K) d) := by
  intro r s h
  apply Subtype.ext
  apply frameFirstMap_injective
  exact congrArg (frameVectorInclusion (d+2)) h

lemma frameHomogeneousVector_finrank (d : ℕ) :
    finrank K (Fin 5 → FrameHomogeneous K d) = 5 * (d+3).choose 3 := by
  rw [Module.finrank_pi_fintype]
  simp only [four_variable_homogeneous_finrank, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end
end PfaffianDescent
