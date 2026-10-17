import PfaffianDescent.GrassmannianHomogeneousFrame

/-!
# Projective transitions for equal free frames

Two free frames that span the same submodule have explicit mutually inverse
coordinate changes.  This is the linear datum from which the projective
transition maps for the Grassmannian-chart families are constructed.
-/

namespace PfaffianDescent

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : Type w} [AddCommGroup V] [Module R V]

/-- The linear combination map of a finite frame. -/
noncomputable abbrev projectiveFrameMap (q : ι → V) : (ι → R) →ₗ[R] V :=
  Fintype.linearCombination R q

/-- A retraction supplies coordinates in a chosen frame. -/
noncomputable def projectiveFrameTransition (q _r : ι → V)
    (retractR : V →ₗ[R] (ι → R)) :
    (ι → R) →ₗ[R] (ι → R) :=
  retractR.comp (projectiveFrameMap q)

lemma projectiveFrameMap_apply_basisFun (q : ι → V) (i : ι) :
    projectiveFrameMap q (Pi.basisFun R ι i) = q i := by
  rw [Fintype.linearCombination_apply]
  classical
  simp [Pi.basisFun_apply]

/-- On the span of a frame, a left coordinate retraction is also a right
inverse to its linear-combination map. -/
lemma projectiveFrameMap_retraction_eq_of_mem_span
    (r : ι → V) (retractR : V →ₗ[R] (ι → R))
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    {x : V} (hx : x ∈ Submodule.span R (Set.range r)) :
    projectiveFrameMap r (retractR x) = x := by
  refine Submodule.span_induction (p := fun x _ =>
    projectiveFrameMap r (retractR x) = x) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    have h := LinearMap.congr_fun hretractR (Pi.basisFun R ι i)
    have hr : retractR (r i) = Pi.basisFun R ι i := by
      simpa [LinearMap.comp_apply, projectiveFrameMap_apply_basisFun] using h
    rw [hr, projectiveFrameMap_apply_basisFun]
  · simp
  · intro x y _ _ hx hy
    simpa using congrArg₂ (· + ·) hx hy
  · intro a x _ hx
    simpa using congrArg (fun z => a • z) hx

/-- Re-expressing the first frame in the second frame gives back the first
linear-combination map whenever its span is contained in the second span. -/
lemma projectiveFrameMap_comp_transition
    (q r : ι → V) (retractR : V →ₗ[R] (ι → R))
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hqr : Submodule.span R (Set.range q) ≤ Submodule.span R (Set.range r)) :
    (projectiveFrameMap r).comp
      (projectiveFrameTransition q r retractR) = projectiveFrameMap q := by
  apply LinearMap.ext
  intro c
  change projectiveFrameMap r (retractR (projectiveFrameMap q c)) = _
  apply projectiveFrameMap_retraction_eq_of_mem_span r retractR hretractR
  apply hqr
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Passing through an intermediate frame does not change the coordinate
transition. This supplies the linear triple-overlap cocycle. -/
lemma projectiveFrameTransition_cocycle
    (q r s : ι → V) (retractR retractS : V →ₗ[R] (ι → R))
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hqr : Submodule.span R (Set.range q) ≤ Submodule.span R (Set.range r)) :
    (projectiveFrameTransition r s retractS).comp
      (projectiveFrameTransition q r retractR) =
        projectiveFrameTransition q s retractS := by
  unfold projectiveFrameTransition
  rw [LinearMap.comp_assoc]
  exact congrArg (fun f => retractS.comp f)
    (projectiveFrameMap_comp_transition q r retractR hretractR hqr)

/-- Equal spans make the two coordinate transitions inverse linear maps. -/
lemma projectiveFrameTransition_comp
    (q r : ι → V) (retractQ retractR : V →ₗ[R] (ι → R))
    (hretractQ : retractQ.comp (projectiveFrameMap q) = LinearMap.id)
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hspan : Submodule.span R (Set.range q) = Submodule.span R (Set.range r)) :
    (projectiveFrameTransition r q retractQ).comp
      (projectiveFrameTransition q r retractR) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  change retractQ (projectiveFrameMap r
    (retractR (projectiveFrameMap q c))) = c
  rw [projectiveFrameMap_retraction_eq_of_mem_span r retractR hretractR]
  exact LinearMap.congr_fun hretractQ c
  apply hspan.le
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Matrix form of the inverse transition identity. -/
lemma projectiveFrameTransition_toMatrix_mul
    (q r : ι → V) (retractQ retractR : V →ₗ[R] (ι → R))
    (hretractQ : retractQ.comp (projectiveFrameMap q) = LinearMap.id)
    (hretractR : retractR.comp (projectiveFrameMap r) = LinearMap.id)
    (hspan : Submodule.span R (Set.range q) = Submodule.span R (Set.range r)) :
    LinearMap.toMatrix' (projectiveFrameTransition r q retractQ) *
      LinearMap.toMatrix' (projectiveFrameTransition q r retractR) = 1 := by
  rw [← LinearMap.toMatrix'_comp,
    projectiveFrameTransition_comp q r retractQ retractR hretractQ hretractR hspan,
    LinearMap.toMatrix'_id]

end PfaffianDescent
