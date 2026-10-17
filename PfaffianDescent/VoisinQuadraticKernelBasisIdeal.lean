import PfaffianDescent.VoisinQuadraticKernelBlockChart
import PfaffianDescent.VoisinQuadraticKernelPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import PfaffianDescent.TripleCompleteIntersectionHilbert

/-!
# The complete-intersection ideal does not depend on a quadratic-pencil basis

The selected split witness is expressed by two particular quadrics, while
the local kernel chart produces a different basis.  Both pairs generate the
same polynomial ideal whenever they are bases of the same quadratic space.
-/

namespace PfaffianDescent

open MvPolynomial Module AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

private theorem basis_image_mem_ideal_span_other_basis
    {K : Type u} [CommRing K]
    {W : Type v} [AddCommGroup W] [Module K W]
    (b c : Basis (Fin 2) K W)
    (f : W →ₗ[K] MvPolynomial (Fin 4) K)
    (i : Fin 2) :
    f (b i) ∈ Ideal.span (Set.range (fun j : Fin 2 => f (c j))) := by
  have hrepr := c.sum_repr (b i)
  have hpoly :
      f (b i) = ∑ j : Fin 2,
        MvPolynomial.C (c.repr (b i) j) * f (c j) := by
    have h := congrArg f hrepr
    simpa only [map_sum, map_smul, MvPolynomial.smul_eq_C_mul] using h.symm
  rw [hpoly]
  apply Submodule.sum_mem
  intro j hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- Two bases of one quadratic vector space define identical ideals after
embedding that space into the homogeneous polynomial ring. -/
theorem ideal_span_basis_image_eq
    {K : Type u} [CommRing K]
    {W : Type v} [AddCommGroup W] [Module K W]
    (b c : Basis (Fin 2) K W)
    (f : W →ₗ[K] MvPolynomial (Fin 4) K) :
    Ideal.span (Set.range (fun i : Fin 2 => f (b i))) =
      Ideal.span (Set.range (fun i : Fin 2 => f (c i))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact basis_image_mem_ideal_span_other_basis b c f i
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact basis_image_mem_ideal_span_other_basis c b f i

/-- The polynomial ideal of a rank-two quadratic restriction kernel depends
only on the kernel submodule, not on its chosen basis or evaluation matrix. -/
theorem ideal_span_quadraticKernelBases_of_kernel_eq
    {K : Type u} [CommRing K]
    (z y : Fin 8 → Fin 4 → K)
    (hker : LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix z)) =
      LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix z))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    Ideal.span (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (b i).1)) =
    Ideal.span (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (c i).1)) := by
  let e := LinearEquiv.ofEq _ _ hker
  let b' := b.map e
  let f := (quadraticPolynomialOfCoefficientsLinearMap K).comp
    (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))).subtype
  have hf (v : LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix y))) :
      f v = quadraticPolynomialOfCoefficients v.1 := rfl
  have h := ideal_span_basis_image_eq b' c f
  simp only [hf, b', Basis.map_apply, e, LinearEquiv.coe_ofEq_apply] at h
  exact h

/-- A fixed cubic can be added to either generating set when the quadratic
evaluation kernels agree. -/
theorem ideal_span_cubic_quadraticKernelBases_of_kernel_eq
    {K : Type u} [CommRing K]
    (p : MvPolynomial (Fin 4) K)
    (z y : Fin 8 → Fin 4 → K)
    (hker : LinearMap.ker (Matrix.toLin'
      (eightPointQuadraticEvaluationMatrix z)) =
      LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix z))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (b i).1))) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (c i).1))) := by
  rw [Ideal.span_insert, Ideal.span_insert,
    ideal_span_quadraticKernelBases_of_kernel_eq z y hker b c]

/-- Any two bases of the quadratic evaluation kernel give the same ideal
after relabeling the eight evaluation points. -/
theorem ideal_span_quadraticKernelBases_relabel
    {K : Type u} [CommRing K]
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → K)
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix (fun i => y (σ i))))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    Ideal.span (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (b i).1)) =
    Ideal.span (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (c i).1)) := by
  exact ideal_span_quadraticKernelBases_of_kernel_eq
    (fun i => y (σ i)) y
    (eightPointQuadraticEvaluationKernel_relabel σ y) b c

/-- Adding the fixed cubic preserves the relabeling invariance of the
quadratic-kernel ideal. -/
theorem ideal_span_cubic_quadraticKernelBases_relabel
    {K : Type u} [CommRing K]
    (p : MvPolynomial (Fin 4) K)
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → K)
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix (fun i => y (σ i))))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (b i).1))) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients (c i).1))) := by
  rw [Ideal.span_insert, Ideal.span_insert,
    ideal_span_quadraticKernelBases_relabel σ y b c]

private theorem range_fin_two_eq_pair {α : Type*} (g : Fin 2 → α) :
    Set.range g = {g 0, g 1} := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro ha
    rcases ha with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

/-- The homogeneous cubic--quadric--quadric intersection ideal constructed
from a basis of the quadratic kernel is independent of relabeling. -/
theorem tripleCompleteIntersectionHomogeneousIdeal_kernelBases_relabel
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → K)
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix (fun i => y (σ i))))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticPolynomialOfCoefficients (b 0).1)
      (quadraticPolynomialOfCoefficients (b 1).1) hp
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1) =
    tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticPolynomialOfCoefficients (c 0).1)
      (quadraticPolynomialOfCoefficients (c 1).1) hp
      (quadraticPolynomialOfCoefficients_isHomogeneous (c 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (c 1).1) := by
  apply HomogeneousIdeal.ext
  change Ideal.span ({p, quadraticPolynomialOfCoefficients (b 0).1,
      quadraticPolynomialOfCoefficients (b 1).1} : Set _) =
    Ideal.span ({p, quadraticPolynomialOfCoefficients (c 0).1,
      quadraticPolynomialOfCoefficients (c 1).1} : Set _)
  simpa only [range_fin_two_eq_pair] using
    (ideal_span_cubic_quadraticKernelBases_relabel p σ y b c)

/-- Relabeling the eight points preserves the resulting projective
complete-intersection scheme, even if a new quadratic-kernel basis is chosen. -/
theorem tripleCompleteIntersectionScheme_kernelBases_relabel
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (σ : Equiv.Perm (Fin 8)) (y : Fin 8 → Fin 4 → K)
    (b : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix (fun i => y (σ i))))))
    (c : Basis (Fin 2) K
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix y)))) :
    scheme (tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticPolynomialOfCoefficients (b 0).1)
      (quadraticPolynomialOfCoefficients (b 1).1) hp
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1)) =
    scheme (tripleCompleteIntersectionHomogeneousIdeal p
      (quadraticPolynomialOfCoefficients (c 0).1)
      (quadraticPolynomialOfCoefficients (c 1).1) hp
      (quadraticPolynomialOfCoefficients_isHomogeneous (c 0).1)
      (quadraticPolynomialOfCoefficients_isHomogeneous (c 1).1)) := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_kernelBases_relabel p hp σ y b c]

private theorem mem_ideal_span_pair_of_mem_linear_span_pair
    {K : Type u} [Field K]
    (q r t : MvPolynomial (Fin 4) K)
    (ht : t ∈ Submodule.span K ({q, r} : Set _)) :
    t ∈ Ideal.span ({q, r} : Set _) := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp ht
  apply Ideal.mem_span_pair.mpr
  refine ⟨MvPolynomial.C a, MvPolynomial.C b, ?_⟩
  simpa only [MvPolynomial.smul_eq_C_mul] using hab

/-- Equality of two quadratic linear spans implies equality of the
polynomial ideals they generate. This applies directly to the checked
span equality for the selected split-quadrics witness. -/
theorem ideal_span_pair_eq_of_linear_span_pair_eq
    {K : Type u} [Field K]
    (q r q' r' : MvPolynomial (Fin 4) K)
    (hspan : Submodule.span K ({q, r} : Set _) =
      Submodule.span K ({q', r'} : Set _)) :
    Ideal.span ({q, r} : Set _) = Ideal.span ({q', r'} : Set _) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t ∈ Submodule.span K ({q', r'} : Set _) := by
      rw [← hspan]
      exact Submodule.subset_span ht
    exact mem_ideal_span_pair_of_mem_linear_span_pair q' r' t ht'
  · apply Ideal.span_le.mpr
    intro t ht
    have ht' : t ∈ Submodule.span K ({q, r} : Set _) := by
      rw [hspan]
      exact Submodule.subset_span ht
    exact mem_ideal_span_pair_of_mem_linear_span_pair q r t ht'

/-- Adding the fixed cubic preserves equality of the two complete-
intersection ideals. -/
theorem ideal_span_cubic_quadratic_pair_eq_of_linear_span_pair_eq
    {K : Type u} [Field K]
    (p q r q' r' : MvPolynomial (Fin 4) K)
    (hspan : Submodule.span K ({q, r} : Set _) =
      Submodule.span K ({q', r'} : Set _)) :
    Ideal.span ({p, q, r} : Set _) =
      Ideal.span ({p, q', r'} : Set _) := by
  calc
    Ideal.span (insert p ({q, r} : Set _)) =
        Ideal.span ({p} : Set _) ⊔ Ideal.span ({q, r} : Set _) :=
      Ideal.span_insert p ({q, r} : Set _)
    _ = Ideal.span ({p} : Set _) ⊔ Ideal.span ({q', r'} : Set _) := by
      rw [ideal_span_pair_eq_of_linear_span_pair_eq q r q' r' hspan]
    _ = Ideal.span (insert p ({q', r'} : Set _)) :=
      (Ideal.span_insert p ({q', r'} : Set _)).symm

/-- The same result in the homogeneous quadratic space used by the
restriction-kernel theorems: equality of homogeneous pencils implies
equality of their cubic--quadric--quadric equations. -/
theorem ideal_span_cubic_homogeneous_quadratic_pair_eq
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (q r q' r' : MvPolynomial.homogeneousSubmodule (Fin 4) K 2)
    (hspan : Submodule.span K ({q, r} : Set _) =
      Submodule.span K ({q', r'} : Set _)) :
    Ideal.span ({p, q.1, r.1} : Set (MvPolynomial (Fin 4) K)) =
      Ideal.span ({p, q'.1, r'.1} : Set (MvPolynomial (Fin 4) K)) := by
  have hmap := congrArg
    (Submodule.map (MvPolynomial.homogeneousSubmodule (Fin 4) K 2).subtype)
    hspan
  have hspan' :
      Submodule.span K ({q.1, r.1} : Set (MvPolynomial (Fin 4) K)) =
        Submodule.span K ({q'.1, r'.1} : Set (MvPolynomial (Fin 4) K)) := by
    simpa [Submodule.map_span, Set.image_pair] using hmap
  exact ideal_span_cubic_quadratic_pair_eq_of_linear_span_pair_eq
    p q.1 r.1 q'.1 r'.1 hspan'

/-- The equality reaches the homogeneous complete-intersection ideals
used to define Voisin's residual scheme. -/
theorem tripleCompleteIntersectionHomogeneousIdeal_toIdeal_eq_of_quadratic_span
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q r q' r' : MvPolynomial.homogeneousSubmodule (Fin 4) K 2)
    (hspan : Submodule.span K ({q, r} : Set _) =
      Submodule.span K ({q', r'} : Set _)) :
    (tripleCompleteIntersectionHomogeneousIdeal p q.1 r.1 hp q.2 r.2).toIdeal =
      (tripleCompleteIntersectionHomogeneousIdeal p q'.1 r'.1 hp q'.2 r'.2).toIdeal := by
  change Ideal.span ({p, q.1, r.1} : Set (MvPolynomial (Fin 4) K)) =
    Ideal.span ({p, q'.1, r'.1} : Set (MvPolynomial (Fin 4) K))
  exact ideal_span_cubic_homogeneous_quadratic_pair_eq p q r q' r' hspan

/-- Thus the projective complete-intersection schemes use literally the
same homogeneous ideal after a quadratic-pencil basis change. -/
theorem tripleCompleteIntersectionHomogeneousIdeal_eq_of_quadratic_span
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q r q' r' : MvPolynomial.homogeneousSubmodule (Fin 4) K 2)
    (hspan : Submodule.span K ({q, r} : Set _) =
      Submodule.span K ({q', r'} : Set _)) :
    tripleCompleteIntersectionHomogeneousIdeal p q.1 r.1 hp q.2 r.2 =
      tripleCompleteIntersectionHomogeneousIdeal p q'.1 r'.1 hp q'.2 r'.2 := by
  apply HomogeneousIdeal.ext
  exact tripleCompleteIntersectionHomogeneousIdeal_toIdeal_eq_of_quadratic_span
    p hp q r q' r' hspan

end PfaffianDescent
