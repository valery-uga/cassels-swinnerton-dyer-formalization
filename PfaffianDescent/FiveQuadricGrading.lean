import PfaffianDescent.FiveQuadricResolution

namespace PfaffianDescent.FiveQuadricResolution
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

lemma lastMap_homogeneous (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    (S.lastMap (frameVectorInclusion d v)).IsHomogeneous (d+2) := by
  change (∑ i, (v i).val * S.quadrics i) ∈ FrameHomogeneous K (d+2)
  exact Submodule.sum_mem _ fun i _ => (v i).property.mul (S.quadrics_homogeneous i)

lemma middleMap_homogeneous (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) (i : Fin 5) :
    (S.middleMap (frameVectorInclusion d v) i).IsHomogeneous (d+1) := by
  change (∑ j, S.matrix i j * (v j).val) ∈ FrameHomogeneous K (d+1)
  apply Submodule.sum_mem
  intro j _
  change (S.matrix i j * (v j).val).IsHomogeneous (d+1)
  have h := (S.matrix_homogeneous i j).mul (v j).property
  simpa only [Nat.add_comm 1 d] using h

noncomputable def gradedLast (d : ℕ) :
    (Fin 5 → FrameHomogeneous K d) →ₗ[K] FrameHomogeneous K (d+2) :=
  ((S.lastMap.restrictScalars K).comp (frameVectorInclusion d)).codRestrict _
    (S.lastMap_homogeneous d)

noncomputable def gradedMiddle (d : ℕ) :
    (Fin 5 → FrameHomogeneous K d) →ₗ[K] (Fin 5 → FrameHomogeneous K (d+1)) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (S.middleMap.restrictScalars K)).comp
      (frameVectorInclusion d)).codRestrict _ (fun v => S.middleMap_homogeneous d v i)

noncomputable def gradedFirst (d : ℕ) :
    FrameHomogeneous K d →ₗ[K] (Fin 5 → FrameHomogeneous K (d+2)) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (S.firstMap.restrictScalars K)).comp
      (FrameHomogeneous K d).subtype).codRestrict _
      (fun r => r.property.mul (S.quadrics_homogeneous i))

@[simp] lemma gradedLast_val (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    (S.gradedLast d v).val = S.lastMap (frameVectorInclusion d v) := rfl

@[simp] lemma gradedMiddle_val (d : ℕ) (v : Fin 5 → FrameHomogeneous K d) :
    frameVectorInclusion (d+1) (S.gradedMiddle d v) = S.middleMap (frameVectorInclusion d v) := rfl

@[simp] lemma gradedFirst_val (d : ℕ) (r : FrameHomogeneous K d) :
    frameVectorInclusion (d+2) (S.gradedFirst d r) = S.firstMap r.val := rfl

lemma gradedFirst_injective (d : ℕ) : Function.Injective (S.gradedFirst d) := by
  intro r s h
  apply Subtype.ext
  apply S.firstMap_injective
  exact congrArg (frameVectorInclusion (d+2)) h

lemma lastMap_component (d : ℕ) (v : Fin 5 → MvPolynomial (Fin 4) K) :
    S.lastMap (fun i => homogeneousComponent d (v i)) =
      homogeneousComponent (d+2) (S.lastMap v) := by
  change (∑ i, homogeneousComponent d (v i) * S.quadrics i) =
    homogeneousComponent (d+2) (∑ i, v i * S.quadrics i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (homogeneousComponent_mul_right (S.quadrics_homogeneous i) d).symm

lemma middleMap_component (d : ℕ) (v : Fin 5 → MvPolynomial (Fin 4) K) (i : Fin 5) :
    S.middleMap (fun j => homogeneousComponent d (v j)) i =
      homogeneousComponent (d+1) (S.middleMap v i) := by
  change (∑ j, S.matrix i j * homogeneousComponent d (v j)) =
    homogeneousComponent (d+1) (∑ j, S.matrix i j * v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.add_comm 1 d] using
    (homogeneousComponent_mul_left (S.matrix_homogeneous i j) d).symm

/-- Exactness at the first rank-five module holds in every homogeneous degree. -/
theorem gradedFirst_exact (d : ℕ) :
    LinearMap.range (S.gradedFirst d) = LinearMap.ker (S.gradedMiddle (d+2)) := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    apply frameVectorInclusion_injective (d+2+1)
    rw [S.gradedMiddle_val, S.gradedFirst_val, map_zero]
    exact LinearMap.mem_ker.mp (S.first_exact ▸
      (show S.firstMap r.val ∈ LinearMap.range S.firstMap from ⟨r.val, rfl⟩))
  · intro hv
    have h := congrArg (frameVectorInclusion (d+2+1)) hv
    rw [S.gradedMiddle_val, map_zero] at h
    have hm : frameVectorInclusion (d+2) v ∈ LinearMap.ker S.middleMap := h
    have he : LinearMap.range S.firstMap = LinearMap.ker S.middleMap := S.first_exact
    rw [← he] at hm
    obtain ⟨r, hr⟩ := hm
    have hr0 : r * S.quadrics 0 = (v 0).val := congrFun hr 0
    have hh : (r * S.quadrics 0).IsHomogeneous (d+2) := hr0 ▸ (v 0).property
    have hd : r.IsHomogeneous d := homogeneous_of_mul_right
      (S.quadrics_homogeneous 0) (S.quadrics_independent.ne_zero 0) hh
    refine ⟨⟨r, hd⟩, ?_⟩
    apply frameVectorInclusion_injective (d+2)
    exact hr

/-- Projection of an arbitrary syzygy preimage gives a homogeneous preimage. -/
theorem gradedMiddle_exact (d : ℕ) :
    LinearMap.range (S.gradedMiddle d) = LinearMap.ker (S.gradedLast (d+1)) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    rw [S.gradedLast_val, S.gradedMiddle_val]
    exact LinearMap.mem_ker.mp (S.last_exact ▸
      (show S.middleMap (frameVectorInclusion d w) ∈ LinearMap.range S.middleMap from
        ⟨frameVectorInclusion d w, rfl⟩))
  · intro hv
    have h : S.lastMap (frameVectorInclusion (d+1) v) = 0 := congrArg Subtype.val hv
    have hm : frameVectorInclusion (d+1) v ∈ LinearMap.ker S.lastMap := h
    have he : LinearMap.range S.middleMap = LinearMap.ker S.lastMap := S.last_exact
    rw [← he] at hm
    obtain ⟨w, hw⟩ := hm
    let w' : Fin 5 → FrameHomogeneous K d := fun i =>
      ⟨homogeneousComponent d (w i), homogeneousComponent_mem d (w i)⟩
    refine ⟨w', ?_⟩
    apply frameVectorInclusion_injective (d+1)
    funext i
    change S.middleMap (fun j => homogeneousComponent d (w j)) i = (v i).val
    rw [S.middleMap_component, congrFun hw i]
    exact homogeneousComponent_eq_self (v i).property

/-- Degreewise exactness of the quadratic-generator map at the homogeneous ideal. -/
theorem gradedLast_range_iff (d : ℕ) (f : FrameHomogeneous K (d+2)) :
    f ∈ LinearMap.range (S.gradedLast d) ↔ f.val ∈ I := by
  constructor
  · rintro ⟨v, rfl⟩
    exact Eq.mp (congrArg (fun J : Ideal (MvPolynomial (Fin 4) K) =>
      (S.gradedLast d v).val ∈ J) S.image_eq) ⟨frameVectorInclusion d v, rfl⟩
  · intro hf
    have hm : f.val ∈ LinearMap.range S.lastMap := by
      change f.val ∈ LinearMap.range (Fintype.linearCombination _ S.quadrics)
      rw [S.image_eq]
      exact hf
    obtain ⟨v, hv⟩ := hm
    let w : Fin 5 → FrameHomogeneous K d := fun i =>
      ⟨homogeneousComponent d (v i), homogeneousComponent_mem d (v i)⟩
    refine ⟨w, Subtype.ext ?_⟩
    change S.lastMap (fun i => homogeneousComponent d (v i)) = f.val
    rw [S.lastMap_component, hv, homogeneousComponent_eq_self f.property]

end
end PfaffianDescent.FiveQuadricResolution
