import Mathlib.RingTheory.Nullstellensatz
import AllCharacteristics.HomogeneousProjective
import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.ProjectivePoints
import AllCharacteristics.OrderedConfigurationFieldPoints
import AllCharacteristics.OrderedConfigurationSubscheme
import AllCharacteristics.FiniteSubschemeRank
import AllCharacteristics.UniversalHomogeneous
import AllCharacteristics.FieldPointClosedLocus
import PfaffianDescent.FiniteDimensionalFunctionEvaluation
import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.LinearNormalizedProjectivePoint
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Finite point evaluations on a cubic surface

Over an algebraically closed field, a homogeneous form not divisible by the
equation of a cubic surface is nonzero at some nonzero affine-cone point of
that surface.  Combining this separation statement with finite-dimensional
linear algebra gives finite point sets imposing independent conditions on a
system of restricted homogeneous forms.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero affine-cone points on the homogeneous hypersurface `p`. -/
def cubicSurfaceAffinePoints {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) :=
  {x : Fin 4 → K // MvPolynomial.aeval x p = 0 ∧ x ≠ 0}

/-- A selected nonzero affine-cone point gives an actual field-valued point
of the associated projective cubic surface. -/
theorem cubicSurfaceAffinePoint_has_hypersurface_point
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : cubicSurfaceAffinePoints p) :
    ∃ q : (AlgebraicGeometry.Spec (.of K) ⟶
      AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      q ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  exact AllCharacteristics.HomogeneousProjective.hypersurface_point_of_coordinates
    (RingHom.id K) p hp x.1 x.2.2 x.2.1

/-- Evaluation at an affine-cone point descends from the polynomial ring to
the homogeneous coordinate ring of the cubic surface. -/
noncomputable def cubicSurfacePointCoordinateRingEvaluation
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : cubicSurfaceAffinePoints p) :
    AllCharacteristics.HomogeneousProjective.CoordinateRing
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) →ₗ[K] K :=
  (Ideal.Quotient.liftₐ
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal
    (MvPolynomial.aeval x.1) (by
      intro q hq
      change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
      rw [hr, map_mul, x.2.1, zero_mul])).toLinearMap

/-- Evaluation of a homogeneous-coordinate-ring piece at all nonzero
affine-cone points of the cubic surface. -/
noncomputable def cubicSurfaceCoordinatePointEvaluation
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {e d : ℕ}
    (hp : p.IsHomogeneous e) :
    AllCharacteristics.HomogeneousProjective.grading
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d →ₗ[K]
        (cubicSurfaceAffinePoints p → K) where
  toFun q x := cubicSurfacePointCoordinateRingEvaluation p hp x q.1
  map_add' q r := by
    ext x
    exact (cubicSurfacePointCoordinateRingEvaluation p hp x).map_add q.1 r.1
  map_smul' a q := by
    ext x
    exact (cubicSurfacePointCoordinateRingEvaluation p hp x).map_smul a q.1

/-- The quotient map from homogeneous polynomials to one graded piece of the
cubic surface's coordinate ring. -/
noncomputable def cubicSurfaceHomogeneousCoordinateProjection
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K d →ₗ[K]
      AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d :=
  LinearMap.codRestrict
    (AllCharacteristics.HomogeneousProjective.grading
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d)
    ((Ideal.Quotient.mkₐ K
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype)
    (fun q => AllCharacteristics.HomogeneousProjective.polynomial_class_mem_grading
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) q.1 q.2)

/-- Every homogeneous coordinate-ring class has a homogeneous polynomial
representative of the same degree. -/
theorem cubicSurfaceHomogeneousCoordinateProjection_surjective
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ) :
    Function.Surjective (cubicSurfaceHomogeneousCoordinateProjection p hp d) := by
  intro v
  have hvmem := v.2
  change v.1 ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal d at hvmem
  obtain ⟨q, hq, hqv⟩ := hvmem
  refine ⟨⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  exact hqv

/-- A finite-dimensional linear system in a graded coordinate-ring piece has
a linear lift to homogeneous polynomials.  The lift is injective because
reduction modulo the cubic is a left inverse. -/
theorem exists_cubicSurfaceCoordinateSubmodule_homogeneous_lift
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d)) :
    ∃ lift : W →ₗ[K] MvPolynomial.homogeneousSubmodule (Fin 4) K d,
      (∀ w, cubicSurfaceHomogeneousCoordinateProjection p hp d (lift w) = w.1) ∧
      Function.Injective lift := by
  let f := cubicSurfaceHomogeneousCoordinateProjection p hp d
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp d))
  let lift := s.domRestrict W
  have hleft : ∀ w : W, f (lift w) = w.1 := by
    intro w
    have h := LinearMap.congr_fun hs w.1
    exact h
  refine ⟨lift, hleft, ?_⟩
  intro a b hab
  apply Subtype.ext
  rw [← hleft a, ← hleft b, hab]

/-- A homogeneous lift of a coordinate-ring section has no nonzero member in
the defining cubic ideal. -/
theorem cubicSurfaceCoordinateSubmodule_homogeneous_lift_separates
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    (lift : W →ₗ[K] MvPolynomial.homogeneousSubmodule (Fin 4) K d)
    (hleft : ∀ w, cubicSurfaceHomogeneousCoordinateProjection p hp d (lift w) = w.1)
    (w : W)
    (hmem : (lift w).1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    lift w = 0 := by
  have hzero : cubicSurfaceHomogeneousCoordinateProjection p hp d (lift w) = 0 := by
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hwzero : w = 0 := by
    apply Subtype.ext
    change w.1 = 0
    rw [← hleft w, hzero]
  rw [hwzero]
  exact map_zero lift

/-- Evaluation of a homogeneous lift at a cubic-surface cone point agrees
with evaluation of its graded coordinate-ring class. -/
theorem cubicSurfaceHomogeneous_lift_evaluation_eq_coordinate_evaluation
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    (lift : W →ₗ[K] MvPolynomial.homogeneousSubmodule (Fin 4) K d)
    (hleft : ∀ w, cubicSurfaceHomogeneousCoordinateProjection p hp d (lift w) = w.1)
    (w : W) (x : cubicSurfaceAffinePoints p) :
    MvPolynomial.aeval x.1 (lift w).1 =
      cubicSurfaceCoordinatePointEvaluation p hp w.1 x := by
  rw [← hleft w]
  rfl

/-- A finite-dimensional system in a graded coordinate-ring piece is
isomorphic to a homogeneous polynomial subsystem which has trivial
intersection with the defining cubic ideal.  This is the polynomial-system
form needed to apply projective linear-system arguments to sections modulo
the cubic equation. -/
theorem exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialEquiv
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d)) :
    ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (e : W ≃ₗ[K] W'),
      (∀ z ∈ W', z.IsHomogeneous d) ∧
      (∀ z ∈ W', z ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
      (∀ (w : W) (x : cubicSurfaceAffinePoints p),
        MvPolynomial.aeval x.1 (e w : MvPolynomial (Fin 4) K) =
          cubicSurfaceCoordinatePointEvaluation p hp w.1 x) ∧
      Module.finrank K W' = Module.finrank K W := by
  obtain ⟨lift, hleft, hlift⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_homogeneous_lift p hp d W
  let g : W →ₗ[K] MvPolynomial (Fin 4) K :=
    (MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype.comp lift
  have hg : Function.Injective g := by
    intro a b hab
    apply hlift
    apply Subtype.ext
    change ((MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype.comp lift) a =
      ((MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype.comp lift) b at hab
    exact hab
  let W' : Submodule K (MvPolynomial (Fin 4) K) := LinearMap.range g
  let e : W ≃ₗ[K] W' := LinearEquiv.ofInjective g hg
  refine ⟨W', e, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨w, rfl⟩
    change (lift w).1.IsHomogeneous d
    exact (lift w).2
  · intro z hz hmem
    rcases hz with ⟨w, rfl⟩
    have hmem' : (lift w).1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
      change g w ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hmem
      change (lift w).1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hmem
      exact hmem
    have hzero := cubicSurfaceCoordinateSubmodule_homogeneous_lift_separates
      p hp d W lift hleft w hmem'
    change g w = 0
    change (lift w : MvPolynomial (Fin 4) K) = 0
    rw [hzero]
    rfl
  · intro w x
    change MvPolynomial.aeval x.1 (g w) =
      cubicSurfaceCoordinatePointEvaluation p hp w.1 x
    change MvPolynomial.aeval x.1 (lift w).1 =
      cubicSurfaceCoordinatePointEvaluation p hp w.1 x
    exact cubicSurfaceHomogeneous_lift_evaluation_eq_coordinate_evaluation
      p hp d W lift hleft w x
  · change Module.finrank K (LinearMap.range g) = Module.finrank K W
    exact LinearMap.finrank_range_of_inj hg

/-- A finite-dimensional graded coordinate-ring system admits an explicitly
indexed independent homogeneous polynomial frame.  The frame is obtained from
the homogeneous lift and retains both its coordinate-ring evaluations and its
dimension, so it can be used directly as a projective equation system. -/
theorem exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialFrame
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (d : ℕ)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W] :
    ∃ (W' : Submodule K (MvPolynomial (Fin 4) K)) (e : W ≃ₗ[K] W')
      (qW : Fin (Module.finrank K W) → W')
      (q : Fin (Module.finrank K W) → MvPolynomial.homogeneousSubmodule (Fin 4) K d),
      (∀ z ∈ W', z.IsHomogeneous d) ∧
      (∀ z ∈ W', z ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → z = 0) ∧
      (∀ (w : W) (x : cubicSurfaceAffinePoints p),
        MvPolynomial.aeval x.1 (e w : MvPolynomial (Fin 4) K) =
          cubicSurfaceCoordinatePointEvaluation p hp w.1 x) ∧
      Module.finrank K W' = Module.finrank K W ∧
      LinearIndependent K qW ∧ LinearIndependent K q ∧
      (∀ i, (qW i : MvPolynomial (Fin 4) K) = (q i).1) := by
  obtain ⟨W', e, hhom, hseparate, heval, hdim⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_homogeneousPolynomialEquiv p hp d W
  letI : AddCommGroup W' := inferInstance
  letI : Module.Free K W' := Module.Free.of_divisionRing K W'
  letI : Module.Finite K W' := Module.Finite.equiv e
  let b : Module.Basis (Fin (Module.finrank K W)) K W' :=
    Module.finBasisOfFinrankEq K W' hdim
  let lift : W' →ₗ[K] MvPolynomial.homogeneousSubmodule (Fin 4) K d :=
    { toFun := fun z => ⟨z.1, hhom z z.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  have hlift : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    simpa [lift] using congrArg
      (fun z : MvPolynomial.homogeneousSubmodule (Fin 4) K d => z.1) hxy
  refine ⟨W', e, b, fun i => lift (b i), hhom, hseparate, heval, hdim,
    b.linearIndependent,
    b.linearIndependent.map' lift (LinearMap.ker_eq_bot_of_injective hlift), ?_⟩
  intro i
  rfl

/-- A homogeneous positive-degree form outside the principal ideal of `p`
does not vanish at every nonzero affine-cone point of `p`. -/
theorem exists_cubicSurfaceAffinePoint_eval_ne_zero_of_not_mem_span
    {K : Type u} [Field K] [IsAlgClosed K]
    (p q : MvPolynomial (Fin 4) K) {d : ℕ}
    (hq : q.IsHomogeneous d) (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hqnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧ MvPolynomial.aeval x p = 0 ∧
      MvPolynomial.aeval x q ≠ 0 := by
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({p} : Set _)
  by_contra hExists
  have hnone : ∀ x : Fin 4 → K,
      ¬ (x ≠ 0 ∧ MvPolynomial.aeval x p = 0 ∧ MvPolynomial.aeval x q ≠ 0) := by
    intro x hx
    exact hExists ⟨x, hx⟩
  have hqvan : q ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      rw [MvPolynomial.aeval_zero, Algebra.algebraMap_self, RingHom.id_apply,
        MvPolynomial.constantCoeff_eq]
      apply hq.coeff_eq_zero
      simpa using Ne.symm hd.ne'
    · by_contra hqeval
      apply hnone x
      refine ⟨hxzero, ?_, hqeval⟩
      exact hx p (Ideal.subset_span (Set.mem_singleton p))
  let _ : I.IsPrime := by simpa only [I] using hprime
  have hqI : q ∈ I := by
    simpa only [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] using hqvan
  exact hqnot (by simpa only [I] using hqI)

/-- Evaluation of a homogeneous linear system at nonzero affine-cone points
of the cubic surface. -/
noncomputable def cubicSurfacePointEvaluation
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (W : Submodule K (MvPolynomial (Fin 4) K)) :
    W →ₗ[K] (cubicSurfaceAffinePoints p → K) :=
  { toFun := fun q x => MvPolynomial.aeval x.1 q.1
    map_add' := by
      intro q r
      ext x
      exact (MvPolynomial.aeval x.1).map_add q.1 r.1
    map_smul' := by
      intro a q
      ext x
      change MvPolynomial.aeval x.1 (a • q.1) =
        a • MvPolynomial.aeval x.1 q.1
      rw [smul_eq_C_mul, map_mul, MvPolynomial.aeval_C,
        Algebra.algebraMap_self]
      simp only [RingHom.id_apply, smul_eq_mul] }

/-- A finite cone configuration on which no homogeneous degree-`d` form
vanishes identically detects every member of the full degree-`d` homogeneous
linear system. -/
theorem finset_cubicSurfacePointEvaluation_injective_of_no_vanishing
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p)) {d : ℕ}
    (hvanishing : ∀ r : MvPolynomial (Fin 4) K, r.IsHomogeneous d →
      (∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) → r = 0) :
    Function.Injective ((finsetEvaluation s).comp
      (cubicSurfacePointEvaluation p
        (MvPolynomial.homogeneousSubmodule (Fin 4) K d))) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply hvanishing
  · exact (a - b).2
  · intro x hx
    have hvalue := congrFun hab ⟨x, hx⟩
    change MvPolynomial.aeval x.1 a.1 = MvPolynomial.aeval x.1 b.1 at hvalue
    change MvPolynomial.aeval x.1 (a - b).1 = 0
    rw [show (a - b).1 = a.1 - b.1 by rfl, map_sub, hvalue, sub_self]

/-- Evaluating a homogeneous form on a scalar multiple of an affine-cone
vector scales its value by the corresponding power of that scalar. -/
theorem aeval_smul_of_isHomogeneous
    {K σ : Type*} [Field K] (q : MvPolynomial σ K) {d : ℕ}
    (hq : q.IsHomogeneous d) (a : K) (x : σ → K) :
    MvPolynomial.aeval (a • x) q = a ^ d * MvPolynomial.aeval x q := by
  classical
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
    rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial s r hs =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    simp only [Finsupp.prod]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hs' : (∑ i ∈ s.support, s i) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply,
        smul_eq_mul, mul_one] using hs
    rw [hs']
    ring

/-- A homogeneous form which vanishes on a nonzero scalar multiple of a cone
vector also vanishes on the original vector. -/
theorem aeval_eq_zero_of_smul_eq_zero_of_isHomogeneous
    {K σ : Type*} [Field K] (q : MvPolynomial σ K) {d : ℕ}
    (hq : q.IsHomogeneous d) (a : K) (ha : a ≠ 0) (x : σ → K)
    (hzero : MvPolynomial.aeval (a • x) q = 0) :
    MvPolynomial.aeval x q = 0 := by
  rw [aeval_smul_of_isHomogeneous q hq] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero d ha)

/-- Vanishing of a polynomial after a field extension descends to the source
field when both its coefficients and its coordinates are transported by the
same field homomorphism. -/
theorem aeval_eq_zero_of_map_aeval_eq_zero
    {K L σ : Type*} [Field K] [Field L] (f : K →+* L)
    (q : MvPolynomial σ K) (x : σ → K)
    (hzero : MvPolynomial.aeval (f ∘ x) (q.map f) = 0) :
    MvPolynomial.aeval x q = 0 := by
  have hzero' : MvPolynomial.eval₂ f (f ∘ x) q = 0 := by
    rw [MvPolynomial.aeval_def] at hzero
    have hf : (algebraMap L L).comp f = f := by
      ext a
      simp
    rw [MvPolynomial.eval₂_map, hf] at hzero
    exact hzero
  apply f.injective
  simp only [map_zero]
  rw [MvPolynomial.aeval_def]
  simpa using (show f (MvPolynomial.eval x q) = 0 by
    rw [MvPolynomial.eval₂_comp]
    exact hzero')

/-- Evaluation commutes with mapping both coefficients and coordinates along
a field homomorphism. -/
theorem aeval_map_of_fieldHom
    {K L σ : Type*} [Field K] [Field L] (f : K →+* L)
    (q : MvPolynomial σ K) (x : σ → K) :
    MvPolynomial.aeval (f ∘ x) (q.map f) = f (MvPolynomial.aeval x q) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def]
  change MvPolynomial.eval (f ∘ x) (q.map f) = f (MvPolynomial.eval x q)
  exact (MvPolynomial.map_eval f x q).symm

/-- If a homogeneous system separates all prescribed scalar values on a
finite set of cone points, distinct selected vectors cannot be scalar
multiples.  Thus the selected points determine distinct projective
directions. -/
theorem finset_cubicSurfaceAffinePointEvaluation_bijective_no_smul
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {d : ℕ}
    (s : Finset (cubicSurfaceAffinePoints p))
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      (cubicSurfacePointEvaluation p
        (MvPolynomial.homogeneousSubmodule (Fin 4) K d))))
    {x y : cubicSurfaceAffinePoints p} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (a : K) : y.1 ≠ a • x.1 := by
  classical
  intro hscale
  let e : s → K := Pi.single ⟨y, hy⟩ 1
  obtain ⟨q, hq⟩ := hbij.2 e
  have hqx : MvPolynomial.aeval x.1 q.1 = 0 := by
    have h := congrFun hq ⟨x, hx⟩
    change MvPolynomial.aeval x.1 q.1 = e ⟨x, hx⟩ at h
    rw [show e ⟨x, hx⟩ = 0 by simp [e, hxy]] at h
    exact h
  have hqy : MvPolynomial.aeval y.1 q.1 = 1 := by
    have h := congrFun hq ⟨y, hy⟩
    change MvPolynomial.aeval y.1 q.1 = e ⟨y, hy⟩ at h
    simpa [e] using h
  rw [hscale, aeval_smul_of_isHomogeneous q.1 q.2 a x.1, hqx, mul_zero] at hqy
  exact one_ne_zero hqy.symm

/-- The projective-direction separation argument applies to every homogeneous
subsystem whose evaluations on the selected cone points are bijective. -/
theorem finset_cubicSurfaceAffinePointEvaluation_bijective_no_smul_of_homogeneous
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) {d : ℕ}
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (s : Finset (cubicSurfaceAffinePoints p))
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      (cubicSurfacePointEvaluation p W)))
    {x y : cubicSurfaceAffinePoints p} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (a : K) : y.1 ≠ a • x.1 := by
  classical
  intro hscale
  let e : s → K := Pi.single ⟨y, hy⟩ 1
  obtain ⟨q, hq⟩ := hbij.2 e
  have hqx : MvPolynomial.aeval x.1 q.1 = 0 := by
    have h := congrFun hq ⟨x, hx⟩
    change MvPolynomial.aeval x.1 q.1 = e ⟨x, hx⟩ at h
    rw [show e ⟨x, hx⟩ = 0 by simp [e, hxy]] at h
    exact h
  have hqy : MvPolynomial.aeval y.1 q.1 = 1 := by
    have h := congrFun hq ⟨y, hy⟩
    change MvPolynomial.aeval y.1 q.1 = e ⟨y, hy⟩ at h
    simpa [e] using h
  rw [hscale, aeval_smul_of_isHomogeneous q.1 (hhom q.1 q.2) a x.1,
    hqx, mul_zero] at hqy
  exact one_ne_zero hqy.symm

/-- The same projective-direction separation holds for a homogeneous piece
of the actual coordinate ring: a value prescription that separates two
points has a homogeneous polynomial representative, so homogeneity rules out
proportional cone vectors. -/
theorem finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) {d : ℕ}
    (s : Finset (cubicSurfaceAffinePoints p))
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      (cubicSurfaceCoordinatePointEvaluation p hp (d := d))))
    {x y : cubicSurfaceAffinePoints p} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (a : K) : y.1 ≠ a • x.1 := by
  classical
  intro hscale
  let e : s → K := Pi.single ⟨y, hy⟩ 1
  obtain ⟨q, hq⟩ := hbij.2 e
  have hqmem := q.2
  change q.1 ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal d at hqmem
  obtain ⟨r, hrhom, hrq⟩ := hqmem
  have hqx : MvPolynomial.aeval x.1 r = 0 := by
    have h := congrFun hq ⟨x, hx⟩
    change cubicSurfacePointCoordinateRingEvaluation p hp x q.1 = e ⟨x, hx⟩ at h
    rw [← hrq, show e ⟨x, hx⟩ = 0 by simp [e, hxy]] at h
    change MvPolynomial.aeval x.1 r = 0 at h
    exact h
  have hqy : MvPolynomial.aeval y.1 r = 1 := by
    have h := congrFun hq ⟨y, hy⟩
    change cubicSurfacePointCoordinateRingEvaluation p hp y q.1 = e ⟨y, hy⟩ at h
    rw [← hrq] at h
    change MvPolynomial.aeval y.1 r = e ⟨y, hy⟩ at h
    simpa [e] using h
  rw [hscale, aeval_smul_of_isHomogeneous r hrhom a x.1, hqx, mul_zero] at hqy
  exact one_ne_zero hqy.symm

/-- The polynomial no-vanishing condition also detects the actual homogeneous
coordinate-ring sections on the cubic surface. -/
theorem finset_cubicSurfaceCoordinatePointEvaluation_injective_of_no_vanishing
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (s : Finset (cubicSurfaceAffinePoints p))
    {d : ℕ}
    (hvanishing : ∀ r : MvPolynomial (Fin 4) K, r.IsHomogeneous d →
      (∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) → r = 0) :
    Function.Injective ((finsetEvaluation s).comp
      (cubicSurfaceCoordinatePointEvaluation p hp (d := d))) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  let q : AllCharacteristics.HomogeneousProjective.grading
      (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d := a - b
  change q.1 = 0
  have hqmem := q.2
  change q.1 ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal d at hqmem
  obtain ⟨r, hrhom, hrq⟩ := hqmem
  have hqvan : ∀ x ∈ s,
      cubicSurfacePointCoordinateRingEvaluation p hp x q.1 = 0 := by
    intro x hx
    have hvalue := congrFun hab ⟨x, hx⟩
    change cubicSurfacePointCoordinateRingEvaluation p hp x a.1 =
      cubicSurfacePointCoordinateRingEvaluation p hp x b.1 at hvalue
    change cubicSurfacePointCoordinateRingEvaluation p hp x (a.1 - b.1) = 0
    rw [map_sub, hvalue, sub_self]
  have hrvan : ∀ x ∈ s, MvPolynomial.aeval x.1 r = 0 := by
    intro x hx
    have hxq := hqvan x hx
    rw [← hrq] at hxq
    change MvPolynomial.aeval x.1 r = 0 at hxq
    exact hxq
  have hrzero := hvanishing r hrhom hrvan
  rw [← hrq, hrzero]
  rfl

/-- A degree-`d` homogeneous linear system whose only member divisible by
the cubic equation is zero is separated by evaluations on the cubic surface. -/
theorem cubicSurfacePointEvaluation_injective_of_principal_separation
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0) :
    Function.Injective (cubicSurfacePointEvaluation p W) := by
  intro a b hab
  by_contra habne
  let r : W := a - b
  have hrne : r ≠ 0 := sub_ne_zero.mpr habne
  have hrpolyne : r.1 ≠ 0 := by
    intro hrzero
    apply hrne
    exact Subtype.ext hrzero
  have hrhom : r.1.IsHomogeneous d := hhom r.1 r.2
  have hrnot : r.1 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro hrI
    apply hrne
    exact Subtype.ext (hseparate r.1 r.2 hrI)
  obtain ⟨x, hxne, hpx, hxr⟩ :=
    exists_cubicSurfaceAffinePoint_eval_ne_zero_of_not_mem_span
      p r.1 hrhom hd hprime hrnot
  let x' : cubicSurfaceAffinePoints p := ⟨x, hpx, hxne⟩
  have hdiff : cubicSurfacePointEvaluation p W (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  apply hxr
  have hx := congrFun hdiff x'
  change MvPolynomial.aeval x r.1 = 0 at hx
  exact hx

/-- Every positive homogeneous piece of the actual coordinate ring of a
prime cubic surface is separated by evaluations at its nonzero cone points. -/
theorem cubicSurfaceCoordinatePointEvaluation_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) {e d : ℕ} (hp : p.IsHomogeneous e)
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    Function.Injective (cubicSurfaceCoordinatePointEvaluation p hp (d := d)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hvmem := v.2
  change v.1 ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal d at hvmem
  obtain ⟨q, hqhom, hqv⟩ := hvmem
  by_cases hqmem : q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))
  · apply Subtype.ext
    rw [← hqv]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqmem
  · obtain ⟨x, hxne, hpx, hxq⟩ :=
      exists_cubicSurfaceAffinePoint_eval_ne_zero_of_not_mem_span
        p q hqhom hd hprime hqmem
    let x' : cubicSurfaceAffinePoints p := ⟨x, hpx, hxne⟩
    have hx := congrFun hv x'
    change cubicSurfacePointCoordinateRingEvaluation p hp x' v.1 = 0 at hx
    rw [← hqv] at hx
    change MvPolynomial.aeval x q = 0 at hx
    exact (hxq hx).elim

/-- A positive homogeneous coordinate-ring piece on a prime cubic surface
has a finite set of nonzero cone points whose evaluations are an isomorphism
onto the scalar tuples at those points. -/
theorem exists_cubicSurfaceCoordinatePoint_finset_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous 3)
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p),
      s.card = Module.finrank K
        (AllCharacteristics.HomogeneousProjective.grading
          (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d) ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfaceCoordinatePointEvaluation p hp (d := d))) := by
  letI : FiniteDimensional K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d) := by
    rw [← cubicSurfaceProjection_range p hp d]
    infer_instance
  apply exists_finset_evaluation_bijective
  exact cubicSurfaceCoordinatePointEvaluation_injective p hp hd hprime

/-- A finite-dimensional subsystem of one positive homogeneous coordinate-ring
piece is interpolated by exactly its dimension many nonzero affine-cone
points.  This is the coordinate-ring form of finite interpolation: it keeps
the system modulo the defining equation, so it applies in degree three
without including the cubic equation itself as an artificial section. -/
theorem exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) {d : ℕ}
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W] :
    ∃ s : Finset (cubicSurfaceAffinePoints p),
      s.card = Module.finrank K W ∧
      Function.Bijective ((finsetEvaluation s).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) := by
  refine exists_finset_evaluation_bijective (K := K)
    (X := cubicSurfaceAffinePoints p) (V := W)
    ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W) ?_
  intro a b hab
  apply Subtype.ext
  apply cubicSurfaceCoordinatePointEvaluation_injective p hp hd hprime
  exact hab

/-- The projective-direction separation argument applies to a homogeneous
subsystem of a graded coordinate-ring piece as well.  A separating value
prescription has a homogeneous polynomial representative, and homogeneity
therefore rules out proportional cone vectors. -/
theorem finset_cubicSurfaceCoordinateSubmodulePointEvaluation_bijective_no_smul
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) {d : ℕ}
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    (s : Finset (cubicSurfaceAffinePoints p))
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)))
    {x y : cubicSurfaceAffinePoints p} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (a : K) : y.1 ≠ a • x.1 := by
  classical
  intro hscale
  let e : s → K := Pi.single ⟨y, hy⟩ 1
  obtain ⟨q, hq⟩ := hbij.2 e
  have hqmem := q.1.2
  change q.1.1 ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp).toIdeal d at hqmem
  obtain ⟨r, hrhom, hrq⟩ := hqmem
  have hqx : MvPolynomial.aeval x.1 r = 0 := by
    have h := congrFun hq ⟨x, hx⟩
    change cubicSurfacePointCoordinateRingEvaluation p hp x q.1.1 = e ⟨x, hx⟩ at h
    rw [← hrq, show e ⟨x, hx⟩ = 0 by simp [e, hxy]] at h
    change MvPolynomial.aeval x.1 r = 0 at h
    exact h
  have hqy : MvPolynomial.aeval y.1 r = 1 := by
    have h := congrFun hq ⟨y, hy⟩
    change cubicSurfacePointCoordinateRingEvaluation p hp y q.1.1 = e ⟨y, hy⟩ at h
    rw [← hrq] at h
    change MvPolynomial.aeval y.1 r = e ⟨y, hy⟩ at h
    simpa [e] using h
  rw [hscale, aeval_smul_of_isHomogeneous r hrhom a x.1, hqx, mul_zero] at hqy
  exact one_ne_zero hqy.symm

/-- Any `n` no larger than the dimension of a fixed homogeneous subsystem
can be realized by `n` projectively distinct surface points imposing
independent conditions.  This supplies the surjective alternative in the
maximal-rank evaluation needed for Voisin's marked-point argument. -/
theorem exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_surjective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) {d : ℕ}
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (n : ℕ) (hn : n ≤ Module.finrank K W) :
    ∃ t : Finset (cubicSurfaceAffinePoints p), t.card = n ∧
      Function.Surjective ((finsetEvaluation t).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K,
        y.1 ≠ a • x.1 := by
  classical
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_bijective
      p hp hd hprime W
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq
    (s := s) (n := n) (by rw [hscard]; exact hn)
  refine ⟨t, htcard, ?_, ?_⟩
  · exact finsetEvaluation_surjective_of_subset
      ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
      hts hsbij.2
  · intro x hx y hy hxy a
    exact finset_cubicSurfaceCoordinateSubmodulePointEvaluation_bijective_no_smul
      p hp W s hsbij (hts hx) (hts hy) hxy a

/-- Ordered version of the surjective witness, suited to the ordered
configuration spaces used in Voisin's genericity arguments. -/
theorem exists_cubicSurfaceCoordinateSubmodule_ordered_evaluation_surjective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) {d : ℕ}
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (n : ℕ) (hn : n ≤ Module.finrank K W) :
    ∃ e : Fin n ↪ cubicSurfaceAffinePoints p,
      Function.Surjective
        ({ toFun := fun q i =>
             ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
               q (e i)
           map_add' := by
             intro q q'
             ext i
             simp
           map_smul' := by
             intro a q
             ext i
             simp } : W →ₗ[K] (Fin n → K)) ∧
      ∀ i j, i ≠ j → ∀ a : K, (e j).1 ≠ a • (e i).1 := by
  classical
  obtain ⟨t, htcard, hsurj, htdir⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_surjective
      p hp hd hprime W n hn
  let eFin : Fin n ≃ t :=
    (Fintype.equivFinOfCardEq (α := t) (by simpa using htcard)).symm
  let e : Fin n ↪ cubicSurfaceAffinePoints p := eFin.toEmbedding.trans
    (Function.Embedding.subtype fun x : cubicSurfaceAffinePoints p => x ∈ t)
  refine ⟨e, ?_, ?_⟩
  · intro z
    let zt : t → K := fun x => z (eFin.symm x)
    obtain ⟨q, hq⟩ := hsurj zt
    refine ⟨q, ?_⟩
    funext i
    have hvalue := congrFun hq (eFin i)
    change ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
      q (e i) = zt (eFin i) at hvalue
    change ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
      q (e i) = z i
    simpa only [zt, eFin.symm_apply_apply] using hvalue
  · intro i j hij a
    apply htdir (e i) (eFin i).2 (e j) (eFin j).2
    · exact e.injective.ne hij

/-- The ordered interpolation witness remains surjective after every field
extension: its selected section values form an identity submatrix over the
base field and hence over each residue field. -/
theorem exists_cubicSurfaceCoordinateSubmodule_extension_stable_surjective_frame
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) {d : ℕ}
    (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (n : ℕ) (hn : n ≤ Module.finrank K W) :
    ∃ e : Fin n ↪ cubicSurfaceAffinePoints p,
      (∀ i j, i ≠ j → ∀ a : K, (e j).1 ≠ a • (e i).1) ∧
      ∃ q : Fin n → W,
        ∀ {L : Type u} [Field L] (g : K →+* L)
          (z : Fin n → L) (i : Fin n),
          (∑ j : Fin n,
            g (((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
              (q j) (e i)) * z j) = z i := by
  obtain ⟨e, hsurj, hdir⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_ordered_evaluation_surjective
      p hp hd hprime W n hn
  let E : W →ₗ[K] (Fin n → K) :=
    { toFun := fun q i =>
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)
          q (e i)
      map_add' := by
        intro q q'
        ext i
        simp
      map_smul' := by
        intro a q
        ext i
        simp }
  have hsurjE : Function.Surjective E := by
    intro z
    obtain ⟨v, hv⟩ := hsurj z
    exact ⟨v, by funext i; exact congrFun hv i⟩
  obtain ⟨q, hq⟩ :=
    surjective_evaluation_has_extension_stable_interpolation_frame
      (K := K) (V := W) n E hsurjE
  refine ⟨e, hdir, q, ?_⟩
  intro L _ g z i
  exact hq g z i

/-- The ten-dimensional quadratic section space of a prime cubic surface is
interpolated by evaluations at ten actual nonzero points of its affine cone. -/
theorem exists_ten_cubicSurfaceCoordinatePoint_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 10 ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfaceCoordinatePointEvaluation p hp (d := 2))) := by
  obtain ⟨s, hs, hbij⟩ :=
    exists_cubicSurfaceCoordinatePoint_finset_evaluation_bijective
      p hp (d := 2) (by decide) hprime
  refine ⟨s, ?_, hbij⟩
  calc
    s.card = Module.finrank K
        (AllCharacteristics.HomogeneousProjective.grading
          (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) 2) := hs
    _ = 10 := cubicSurface_grade_two_finrank p hp hne

/-- Eight points can be selected from a quadratic interpolation configuration
so that they impose eight independent conditions on the quadratic sections
of the cubic surface.  This is the concrete independent-conditions witness
used in the degree-eight fixed-component argument. -/
theorem exists_eight_cubicSurfaceCoordinatePoint_evaluation_surjective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 8 ∧
      Function.Surjective ((finsetEvaluation s).comp
        (cubicSurfaceCoordinatePointEvaluation p hp (d := 2))) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨t, htcard, htbij⟩ :=
    exists_ten_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  obtain ⟨s, hst, hscard⟩ :=
    Finset.exists_subset_card_eq (s := t) (n := 8) (by omega)
  refine ⟨s, hscard,
    finsetEvaluation_surjective_of_subset
      (cubicSurfaceCoordinatePointEvaluation p hp (d := 2)) hst htbij.2, ?_⟩
  intro x hx y hy hxy a
  exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
    p hp t htbij (hst hx) (hst hy) hxy a

/-- The nineteen-dimensional cubic section space of a prime cubic surface is
interpolated by evaluations at nineteen actual nonzero points of its affine
cone. -/
theorem exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 19 ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfaceCoordinatePointEvaluation p hp (d := 3))) := by
  obtain ⟨s, hs, hbij⟩ :=
    exists_cubicSurfaceCoordinatePoint_finset_evaluation_bijective
      p hp (d := 3) (by decide) hprime
  refine ⟨s, ?_, hbij⟩
  calc
    s.card = Module.finrank K
        (AllCharacteristics.HomogeneousProjective.grading
          (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) 3) := hs
    _ = 19 := cubicSurface_grade_three_finrank p hp hne

/-- A finite-dimensional homogeneous system on a prime cubic surface admits
exactly as many nonzero surface points as its dimension whose evaluations
give every possible tuple of scalar values. -/
theorem exists_cubicSurfaceAffinePoint_finset_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = Module.finrank K W ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p W)) := by
  apply exists_finset_evaluation_bijective
  exact cubicSurfacePointEvaluation_injective_of_principal_separation
    p hd hprime W hhom hseparate

/-- Ten nonzero affine-cone points on a prime cubic surface impose independent
conditions on the full vector space of quadratic forms. -/
theorem exists_ten_cubicSurfaceAffinePoint_quadratic_evaluation_bijective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 10 ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p
          (MvPolynomial.homogeneousSubmodule (Fin 4) K 2))) := by
  obtain ⟨s, hs, hbij⟩ :=
    exists_cubicSurfaceAffinePoint_finset_evaluation_bijective
      p (d := 2) (by decide) hprime
      (MvPolynomial.homogeneousSubmodule (Fin 4) K 2)
      (by
        intro q hq
        exact hq)
      (by
        intro q hq hqmem
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hqmem
        have hrp : r * p = q := by
          rw [mul_comm]
          exact hr.symm
        have hrzero : r = 0 := eq_zero_of_mul_homogeneous_lt hp hne (by
          rw [hrp]
          exact hq) (by decide)
        rw [← hrp, hrzero, zero_mul])
  refine ⟨s, ?_, hbij⟩
  rw [four_variable_homogeneous_finrank] at hs
  norm_num at hs ⊢
  exact hs

/-- A square quadratic interpolation configuration remains a quadratic
non-vanishing witness after arbitrary extension of the ground field.  The
evaluation matrix has a unit inverse over the original field, hence after
coefficient extension as well. -/
theorem quadraticAvoidance_fieldExtension_of_bijective
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p))
    (hscard : s.card = 10)
    (hbij : Function.Bijective ((finsetEvaluation s).comp
      (cubicSurfacePointEvaluation p
        (MvPolynomial.homogeneousSubmodule (Fin 4) K 2))))
    (r : MvPolynomial (Fin 4) L) (hr : r.IsHomogeneous 2)
    (hrvan : ∀ x ∈ s,
      MvPolynomial.aeval (fun i => f (x.1 i)) r = 0) :
    r = 0 := by
  classical
  have hmonomialcard : Fintype.card (Monomials (Fin 4) 2) = 10 := by
    have hdim : Module.finrank K
        (MvPolynomial.homogeneousSubmodule (Fin 4) K 2) =
        Fintype.card (Monomials (Fin 4) 2) := by
      rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
      exact Module.finrank_eq_card_basis
        (MvPolynomial.basisRestrictSupport K {a | a.degree = 2})
    rw [← hdim, four_variable_homogeneous_finrank]
    decide
  have hscard' : Fintype.card s = 10 := by
    simpa only [Fintype.card_coe] using hscard
  let e : Monomials (Fin 4) 2 ≃ s :=
    Fintype.equivOfCardEq (hmonomialcard.trans hscard'.symm)
  let A : Matrix (Monomials (Fin 4) 2) (Monomials (Fin 4) 2) K :=
    fun i j => j.1.prod fun k n => (e i).1.1 k ^ n
  let q : (Monomials (Fin 4) 2 → K) → MvPolynomial (Fin 4) K :=
    fun c => ∑ j, MvPolynomial.monomial j.1 (c j)
  have hqhom (c : Monomials (Fin 4) 2 → K) : (q c).IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact MvPolynomial.isHomogeneous_monomial (c j) j.2
  have hA_eval (c : Monomials (Fin 4) 2 → K) (i : Monomials (Fin 4) 2) :
      A.mulVec c i = MvPolynomial.aeval (e i).1.1 (q c) := by
    simp only [A, q,
      MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hqcoeff (c : Monomials (Fin 4) 2 → K) (j : Monomials (Fin 4) 2) :
      MvPolynomial.coeff j.1 (q c) = c j := by
    dsimp [q]
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : k.1 ≠ j.1 := by
        intro h
        exact hkj (Subtype.ext h)
      simp [hne]
    · simp
  have hAinj : Function.Injective A.mulVec := by
    intro c c' hcc'
    have heval : ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p
          (MvPolynomial.homogeneousSubmodule (Fin 4) K 2)))
        ⟨q c, hqhom c⟩ =
        ((finsetEvaluation s).comp
          (cubicSurfacePointEvaluation p
            (MvPolynomial.homogeneousSubmodule (Fin 4) K 2)))
          ⟨q c', hqhom c'⟩ := by
      ext x
      obtain ⟨i, rfl⟩ := e.surjective x
      change MvPolynomial.aeval (e i).1.1 (q c) =
        MvPolynomial.aeval (e i).1.1 (q c')
      rw [← hA_eval c i, ← hA_eval c' i, hcc']
    have hqeq : q c = q c' :=
      congrArg Subtype.val (hbij.1 heval)
    funext j
    have hcoeff := congrArg (MvPolynomial.coeff j.1) hqeq
    rw [hqcoeff c j, hqcoeff c' j] at hcoeff
    exact hcoeff
  have hAmapinj : Function.Injective (A.map f).mulVec :=
    Matrix.map_mulVec_injective_of_mulVec_injective f A hAinj
  let coeff : Monomials (Fin 4) 2 → L := fun j => r.coeff j.1
  have hAmap_eval (c : Monomials (Fin 4) 2 → L) (i : Monomials (Fin 4) 2) :
      (A.map f).mulVec c i =
        MvPolynomial.aeval (fun k => f ((e i).1.1 k))
          (∑ j, MvPolynomial.monomial j.1 (c j)) := by
    simp only [A,
      MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial,
      Algebra.algebraMap_self, RingHom.id_apply]
    change (∑ j, f (j.1.prod fun k n => (e i).1.1 k ^ n) * c j) =
      ∑ j, c j * j.1.prod fun k n => f ((e i).1.1 k) ^ n
    apply Finset.sum_congr rfl
    intro j _
    simp [map_prod, mul_comm]
  have hcoeffeq : (A.map f).mulVec coeff = 0 := by
    funext i
    rw [hAmap_eval coeff i,
      AllCharacteristics.UniversalHomogeneous.sum_monomial_coeff_eq r hr]
    simpa [coeff] using hrvan (e i).1 (e i).2
  have hcoeffzero : coeff = 0 := hAmapinj (by simpa using hcoeffeq)
  apply MvPolynomial.ext
  intro m
  change r.coeff m = 0
  by_cases hm : m.degree = 2
  · let j : Monomials (Fin 4) 2 := ⟨m, hm⟩
    have hj := congrFun hcoeffzero j
    simpa [coeff, j] using hj
  · exact hr.coeff_eq_zero hm

/-- The ten quadratic interpolation points can be selected in ten distinct
projective directions. -/
theorem exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 10 ∧
      Function.Bijective ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p
          (MvPolynomial.homogeneousSubmodule (Fin 4) K 2))) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hbij⟩ :=
    exists_ten_cubicSurfaceAffinePoint_quadratic_evaluation_bijective
      p hp hne hprime
  refine ⟨s, hscard, hbij, ?_⟩
  intro x hx y hy hxy a
  exact finset_cubicSurfaceAffinePointEvaluation_bijective_no_smul
    p s hbij hx hy hxy a

/-- A finite set of pairwise distinct projective directions cannot cover a
strictly larger direction-separated set by scalar multiples. -/
theorem exists_cubicSurfaceAffinePoint_direction_outside_of_card_lt
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s t : Finset (cubicSurfaceAffinePoints p))
    (hcardlt : s.card < t.card)
    (htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1) :
    ∃ x ∈ t, ∀ y ∈ s, ∀ a : K, x.1 ≠ a • y.1 := by
  classical
  by_contra h
  push Not at h
  choose f hf a ha using h
  let F : t → s := fun x => ⟨f x.1 x.2, hf x.1 x.2⟩
  let A : t → K := fun x => a x.1 x.2
  have hA (x : t) : x.1.1 = A x • (F x).1.1 := ha x.1 x.2
  have hF : Function.Injective F := by
    intro x y hxy
    by_contra hne
    have hneval : x.1 ≠ y.1 := fun he => hne (Subtype.ext he)
    have hAx : A x ≠ 0 := by
      intro hz
      have hxzero : x.1.1 = 0 := by rw [hA, hz, zero_smul]
      exact x.1.2.2 hxzero
    have hprop : y.1.1 = (A y * (A x)⁻¹) • x.1.1 := by
      calc
        y.1.1 = A y • (F y).1.1 := hA y
        _ = A y • (F x).1.1 := by rw [hxy]
        _ = (A y * (A x)⁻¹) • (A x • (F x).1.1) := by
          rw [smul_smul]
          field_simp
        _ = (A y * (A x)⁻¹) • x.1.1 := by rw [← hA x]
    exact htdir x.1 x.2 y.1 y.2 hneval _ hprop
  have hcard : t.card ≤ s.card := by
    calc
      t.card = Fintype.card t := by simp
      _ ≤ Fintype.card s := Fintype.card_le_of_injective F hF
      _ = s.card := by simp
  exact (not_lt_of_ge hcard) hcardlt

/-- For nonzero vectors, exclusion from all scalar multiples is symmetric. -/
theorem not_smul_symm_of_nonzero
    {K σ : Type*} [Field K] (x y : σ → K) (hy : y ≠ 0)
    (hxy : ∀ a : K, x ≠ a • y) (a : K) : y ≠ a • x := by
  intro h
  by_cases ha : a = 0
  · rw [ha, zero_smul] at h
    exact hy h
  apply hxy a⁻¹
  calc
    x = (a⁻¹ * a) • x := by
      rw [inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • (a • x) := by rw [smul_smul]
    _ = a⁻¹ • y := by rw [h]

/-- A direction-separated set of affine-cone points can be enlarged to the
cardinality of another direction-separated set.  The added points are chosen
one at a time outside all scalar directions already present. -/
theorem exists_cubicSurfaceAffinePoint_directionSeparated_superset_of_card_le
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s t : Finset (cubicSurfaceAffinePoints p))
    (hcard : s.card ≤ t.card)
    (hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1)
    (htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), s ⊆ u ∧ u.card = t.card ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ s : Finset (cubicSurfaceAffinePoints p), s.card + n = t.card →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1) →
      ∃ u : Finset (cubicSurfaceAffinePoints p), s ⊆ u ∧ u.card = t.card ∧
        ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hsum hsdir
      by_cases hn : n = 0
      · refine ⟨s, subset_rfl, ?_, hsdir⟩
        omega
      · have hlt : s.card < t.card := by omega
        obtain ⟨x, hxt, hxout⟩ :=
          exists_cubicSurfaceAffinePoint_direction_outside_of_card_lt
            p s t hlt htdir
        have hxnot : x ∉ s := by
          intro hxs
          exact hxout x hxs 1 (by simp)
        let s' : Finset (cubicSurfaceAffinePoints p) := insert x s
        have hs_sub : s ⊆ s' := by
          intro y hy
          exact Finset.mem_insert_of_mem hy
        have hscard' : s'.card = s.card + 1 := by
          exact Finset.card_insert_of_notMem hxnot
        have hcard' : s'.card ≤ t.card := by
          rw [hscard']
          omega
        have hsdir' : ∀ y ∈ s', ∀ z ∈ s', y ≠ z → ∀ a : K,
            z.1 ≠ a • y.1 := by
          intro y hy z hz hyz a
          by_cases hyx : y = x
          · subst y
            by_cases hzx : z = x
            · subst z
              exact (hyz rfl).elim
            · have hzs : z ∈ s := by
                apply (Finset.mem_insert.mp (by simpa [s'] using hz)).resolve_left hzx
              exact not_smul_symm_of_nonzero x.1 z.1 z.2.2
                (fun b => hxout z hzs b) a
          · have hys : y ∈ s := by
              apply (Finset.mem_insert.mp (by simpa [s'] using hy)).resolve_left hyx
            by_cases hzx : z = x
            · subst z
              exact hxout y hys a
            · have hzs : z ∈ s := by
                apply (Finset.mem_insert.mp (by simpa [s'] using hz)).resolve_left hzx
              exact hsdir y hys z hzs hyz a
        have hnlt : n - 1 < n := by omega
        obtain ⟨u, hs'u, hucard, hudir⟩ :=
          ih (n - 1) hnlt s' (by
            rw [hscard']
            omega) hsdir'
        exact ⟨u, hs_sub.trans hs'u, hucard, hudir⟩
  exact hP (t.card - s.card) s (Nat.add_sub_of_le hcard) hsdir

/-- Evaluation of an explicit homogeneous linear form is the expected dot
product of its coefficient and coordinate vectors. -/
theorem homogeneousLinearForm_eval
    {K : Type u} [Field K] (c x : Fin 4 → K) :
    MvPolynomial.aeval x (homogeneousLinearForm c) = ∑ i, c i * x i := by
  unfold homogeneousLinearForm
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- A finite family of nonzero affine-cone vectors has one homogeneous
linear form that is nonzero on every member. -/
theorem exists_common_homogeneousLinearForm_nonzero_on_cubicSurfaceAffinePoints
    {K : Type u} [Field K] [Infinite K] (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p)) :
    ∃ c : Fin 4 → K, ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := K)
    (v := fun x : s => x.1.1) (fun x => x.1.2.2)
  let c : Fin 4 → K := fun i => f (Pi.single i 1)
  refine ⟨c, ?_⟩
  intro x hx
  have hsum : x.1 = ∑ i, x.1 i • Pi.single i 1 := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · simp
  rw [homogeneousLinearForm_eval]
  have hfx : f x.1 ≠ 0 := hf ⟨x, hx⟩
  rw [hsum, map_sum] at hfx
  simpa [c, smul_eq_mul, mul_comm] using hfx

/-- Normalize a nonzero cone vector in the affine chart defined by a linear
form. -/
noncomputable def cubicSurfaceAffinePointNormalizedConeCoordinates
    {K : Type u} [Field K] (c : Fin 4 → K)
    (x : Fin 4 → K) : Fin 4 → K :=
  (MvPolynomial.aeval x (homogeneousLinearForm c))⁻¹ • x

lemma homogeneousLinearForm_isHomogeneous
    {K : Type u} [Field K] (c : Fin 4 → K) :
    (homogeneousLinearForm c).IsHomogeneous 1 := by
  unfold homogeneousLinearForm
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

/-- If a nonempty affine-cone configuration rules out a nonzero quadric,
then it also rules out a nonzero linear form.  Multiplication by a linear
form nonzero at every selected point promotes a linear vanishing relation to
a quadratic one. -/
theorem quadraticAvoidance_linear
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p))
    (c : Fin 4 → K) (hs : s.Nonempty)
    (hcommon : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0)
    (hquad : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
      (∀ x ∈ s, MvPolynomial.aeval x.1 q = 0) → q = 0)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 1)
    (hrvan : ∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) :
    r = 0 := by
  have hell : homogeneousLinearForm c ≠ 0 := by
    obtain ⟨x, hx⟩ := hs
    intro hzero
    exact hcommon x hx (by rw [hzero, map_zero])
  have hmulhom : (r * homogeneousLinearForm c).IsHomogeneous 2 := by
    simpa using hr.mul (homogeneousLinearForm_isHomogeneous c)
  have hmulvan : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (r * homogeneousLinearForm c) = 0 := by
    intro x hx
    rw [map_mul, hrvan x hx, zero_mul]
  have hmulzero := hquad (r * homogeneousLinearForm c) hmulhom hmulvan
  exact (mul_eq_zero.mp hmulzero).resolve_right hell

/-- If a nonempty affine-cone configuration rules out a nonzero quadric,
then it also rules out a nonzero constant homogeneous form. -/
theorem quadraticAvoidance_constant
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p))
    (c : Fin 4 → K) (hs : s.Nonempty)
    (hcommon : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0)
    (hquad : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
      (∀ x ∈ s, MvPolynomial.aeval x.1 q = 0) → q = 0)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 0)
    (hrvan : ∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) :
    r = 0 := by
  have hell : homogeneousLinearForm c ≠ 0 := by
    obtain ⟨x, hx⟩ := hs
    intro hzero
    exact hcommon x hx (by rw [hzero, map_zero])
  have hmulhom : (r * (homogeneousLinearForm c) ^ 2).IsHomogeneous 2 := by
    simpa using hr.mul ((homogeneousLinearForm_isHomogeneous c).pow 2)
  have hmulvan : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (r * (homogeneousLinearForm c) ^ 2) = 0 := by
    intro x hx
    rw [map_mul, hrvan x hx, zero_mul]
  have hmulzero := hquad (r * (homogeneousLinearForm c) ^ 2) hmulhom hmulvan
  exact (mul_eq_zero.mp hmulzero).resolve_right (pow_ne_zero 2 hell)

/-- Quadratic avoidance implies lower-degree avoidance without choosing an
affine chart: multiply by one fixed nonzero coordinate variable.  This form
works for points over any coefficient field, including scalar extensions of a
configuration initially defined over a smaller field. -/
theorem homogeneous_of_le_two_of_quadratic_avoidance
    {K X : Type u} [Field K] (s : Finset X) (coordinates : X → Fin 4 → K)
    (hquad : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
      (∀ x ∈ s, MvPolynomial.aeval (coordinates x) q = 0) → q = 0)
    {e : ℕ} (he : e ≤ 2) (r : MvPolynomial (Fin 4) K)
    (hr : r.IsHomogeneous e)
    (hrvan : ∀ x ∈ s, MvPolynomial.aeval (coordinates x) r = 0) :
    r = 0 := by
  interval_cases e
  · have hmulhom : (r * (MvPolynomial.X 0) ^ 2).IsHomogeneous 2 := by
      simpa using hr.mul ((MvPolynomial.isHomogeneous_X K 0).pow 2)
    have hmulvan : ∀ x ∈ s,
        MvPolynomial.aeval (coordinates x) (r * (MvPolynomial.X 0) ^ 2) = 0 := by
      intro x hx
      rw [map_mul, hrvan x hx, zero_mul]
    have hmulzero := hquad (r * (MvPolynomial.X 0) ^ 2) hmulhom hmulvan
    exact (mul_eq_zero.mp hmulzero).resolve_right
      (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
  · have hmulhom : (r * MvPolynomial.X 0).IsHomogeneous 2 := by
      simpa using hr.mul (MvPolynomial.isHomogeneous_X K 0)
    have hmulvan : ∀ x ∈ s,
        MvPolynomial.aeval (coordinates x) (r * MvPolynomial.X 0) = 0 := by
      intro x hx
      rw [map_mul, hrvan x hx, zero_mul]
    have hmulzero := hquad (r * MvPolynomial.X 0) hmulhom hmulvan
    exact (mul_eq_zero.mp hmulzero).resolve_right (MvPolynomial.X_ne_zero 0)
  · exact hquad r hr hrvan

/-- The deleted-ten-point quadratic Cayley--Bacharach condition also detects
forms of every homogeneous degree at most two after the same deletion.  This
is the form needed when a projective incidence argument produces a constant
or a linear equation instead of a quadric. -/
theorem homogeneous_of_le_two_of_quadratic_cayley_bacharach
    {K X : Type u} [Field K] (s : Finset X) (coordinates : X → Fin 4 → K)
    (hCB : ∀ y ∈ s, ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
      (∀ z ∈ s, z ≠ y → MvPolynomial.aeval (coordinates z) q = 0) → q = 0)
    (y : X) (hy : y ∈ s) {e : ℕ} (he : e ≤ 2)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous e)
    (hrvan : ∀ z ∈ s, z ≠ y → MvPolynomial.aeval (coordinates z) r = 0) :
    r = 0 := by
  interval_cases e
  · have hmulhom : (r * (MvPolynomial.X 0) ^ 2).IsHomogeneous 2 := by
      simpa using hr.mul ((MvPolynomial.isHomogeneous_X K 0).pow 2)
    have hmulvan : ∀ z ∈ s, z ≠ y →
        MvPolynomial.aeval (coordinates z) (r * (MvPolynomial.X 0) ^ 2) = 0 := by
      intro z hz hzy
      rw [map_mul, hrvan z hz hzy, zero_mul]
    have hmulzero := hCB y hy (r * (MvPolynomial.X 0) ^ 2) hmulhom hmulvan
    exact (mul_eq_zero.mp hmulzero).resolve_right
      (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
  · have hmulhom : (r * MvPolynomial.X 0).IsHomogeneous 2 := by
      simpa using hr.mul (MvPolynomial.isHomogeneous_X K 0)
    have hmulvan : ∀ z ∈ s, z ≠ y →
        MvPolynomial.aeval (coordinates z) (r * MvPolynomial.X 0) = 0 := by
      intro z hz hzy
      rw [map_mul, hrvan z hz hzy, zero_mul]
    have hmulzero := hCB y hy (r * MvPolynomial.X 0) hmulhom hmulvan
    exact (mul_eq_zero.mp hmulzero).resolve_right (MvPolynomial.X_ne_zero 0)
  · exact hCB y hy r hr hrvan

/-- Quadratic avoidance on a nonempty cone configuration gives injective
evaluation on every homogeneous degree at most two. -/
theorem quadraticAvoidance_homogeneous_of_le_two
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K)
    (s : Finset (cubicSurfaceAffinePoints p))
    (c : Fin 4 → K) (hs : s.Nonempty)
    (hcommon : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0)
    (hquad : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
      (∀ x ∈ s, MvPolynomial.aeval x.1 q = 0) → q = 0)
    {e : ℕ} (he : e ≤ 2) (r : MvPolynomial (Fin 4) K)
    (hr : r.IsHomogeneous e)
    (hrvan : ∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) :
    r = 0 := by
  interval_cases e
  · exact quadraticAvoidance_constant p s c hs hcommon hquad r hr hrvan
  · exact quadraticAvoidance_linear p s c hs hcommon hquad r hr hrvan
  · exact hquad r hr hrvan

lemma cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval
    {K : Type u} [Field K] (c : Fin 4 → K) (x : Fin 4 → K)
    (hx : MvPolynomial.aeval x (homogeneousLinearForm c) ≠ 0) :
    MvPolynomial.aeval (cubicSurfaceAffinePointNormalizedConeCoordinates c x)
      (homogeneousLinearForm c) = 1 := by
  rw [cubicSurfaceAffinePointNormalizedConeCoordinates,
    aeval_smul_of_isHomogeneous _ (homogeneousLinearForm_isHomogeneous c), pow_one,
    inv_mul_cancel₀ hx]

lemma cubicSurfaceAffinePointNormalizedConeCoordinates_surface_eval
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p) :
    MvPolynomial.aeval (cubicSurfaceAffinePointNormalizedConeCoordinates c x.1) p = 0 := by
  rw [cubicSurfaceAffinePointNormalizedConeCoordinates,
    aeval_smul_of_isHomogeneous _ hp, x.2.1, mul_zero]

/-- The normalized affine coordinates define a specified actual field-valued
point of the cubic surface in the common linear chart. -/
noncomputable def cubicSurfaceAffinePointLinearNormalizedProjectivePoint
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    AlgebraicGeometry.Spec (.of K) ⟶
      AllCharacteristics.HomogeneousProjective.hypersurface p hp :=
  linearNormalizedPoint
    (AllCharacteristics.HomogeneousProjective.equationIdeal p hp)
    (cubicSurfaceAffinePointNormalizedConeCoordinates c x.1) (homogeneousLinearForm c)
    (homogeneousLinearForm_isHomogeneous c)
    (cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval c x.1 hx) (by
      intro q hq
      change MvPolynomial.aeval (cubicSurfaceAffinePointNormalizedConeCoordinates c x.1) q = 0
      change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
      rw [hr, map_mul,
        cubicSurfaceAffinePointNormalizedConeCoordinates_surface_eval p hp c x, zero_mul])

/-- The normalized projective point lies over the original field point. -/
theorem cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
      AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  exact linearNormalizedPoint_toBase _ _ _ _ _ _

/-- The ambient projective image of a linearly normalized affine-cone point
has an exact presentation in one ordinary coordinate chart.  Its chart
coordinates are the original cone coordinates divided by the chosen nonzero
coordinate. -/
theorem exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    ∃ (j : Fin 4) (u : Kˣ)
      (g : Away (MvPolynomial.homogeneousSubmodule (Fin 4) K) (MvPolynomial.X j) →+* K),
      (u : K) = cubicSurfaceAffinePointNormalizedConeCoordinates c x.1 j ∧
        (∀ i : Fin 4,
          g (AllCharacteristics.GradedChart.normalized
            (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X K i)) =
              (↑(u⁻¹) : K) * cubicSurfaceAffinePointNormalizedConeCoordinates c x.1 i) ∧
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide : 0 < 1) =
          cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
            AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp := by
  let n : Fin 4 → K := cubicSurfaceAffinePointNormalizedConeCoordinates c x.1
  have hn : n ≠ 0 := by
    intro hn
    have h := cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval c x.1 hx
    rw [homogeneousLinearForm_eval,
      show cubicSurfaceAffinePointNormalizedConeCoordinates c x.1 = n by rfl, hn] at h
    simpa using h
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, n j ≠ 0 := by
    by_contra h
    apply hn
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let u : Kˣ := Units.mk0 (n j) hj
  have hu : (u : K) = n j := by simp [u]
  let I := AllCharacteristics.HomogeneousProjective.equationIdeal p hp
  let ell := homogeneousLinearForm c
  have hell : ell.IsHomogeneous 1 := homogeneousLinearForm_isHomogeneous c
  have hxell : ell.eval₂ (algebraMap K K) n = 1 := by
    change MvPolynomial.aeval n ell = 1
    exact cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval c x.1 hx
  have he : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K K) n = 0 := by
    intro q hq
    change MvPolynomial.aeval n q = 0
    change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    rw [hr, map_mul,
      cubicSurfaceAffinePointNormalizedConeCoordinates_surface_eval p hp c x, zero_mul]
  obtain ⟨gI, hgIcoords, hgIpoint⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint I n ell hell hxell he j u hu
  let g := gI.comp
    (AllCharacteristics.HomogeneousProjective.hypersurfaceAmbientChartMap p hp j)
  refine ⟨j, u, g, hu, ?_, ?_⟩
  · intro i
    change gI (AllCharacteristics.HomogeneousProjective.hypersurfaceAmbientChartMap p hp j
      (AllCharacteristics.GradedChart.normalized
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)
        (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i))) = _
    rw [AllCharacteristics.HomogeneousProjective.hypersurfaceAmbientChartMap_coordinate]
    exact hgIcoords i
  · calc
      Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide : 0 < 1) =
        Spec.map (CommRingCat.ofHom gI) ≫
          (Spec.map (CommRingCat.ofHom
            (AllCharacteristics.HomogeneousProjective.hypersurfaceAmbientChartMap p hp j)) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
                (by decide : 0 < 1)) := by
          rw [← Category.assoc, ← Spec.map_comp]
          rfl
      _ = Spec.map (CommRingCat.ofHom gI) ≫
          (AllCharacteristics.HomogeneousProjective.chartι I j ≫
            AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) := by
          rw [AllCharacteristics.HomogeneousProjective.chartι_comp_hypersurfaceToAmbient]
      _ = (Spec.map (CommRingCat.ofHom gI) ≫
          AllCharacteristics.HomogeneousProjective.chartι I j) ≫
            AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp := by
          dsimp only [I]
          exact (Category.assoc _ _ _).symm
      _ = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
          AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp := by
          dsimp only [I] at hgIpoint
          rw [hgIpoint]
          rfl

/-- The ambient chart presentation of a normalized marked cubic-surface point
persists after an arbitrary extension of its ground field. -/
theorem exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint_fieldExtension
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    ∃ (j : Fin 4) (u : Kˣ)
      (g : Away (MvPolynomial.homogeneousSubmodule (Fin 4) K) (MvPolynomial.X j) →+* L),
      (u : K) = cubicSurfaceAffinePointNormalizedConeCoordinates c x.1 j ∧
        (∀ i : Fin 4,
          g (AllCharacteristics.GradedChart.normalized
            (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X K i)) =
              f ((↑(u⁻¹) : K) * cubicSurfaceAffinePointNormalizedConeCoordinates c x.1 i)) ∧
        Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide : 0 < 1) =
          Spec.map (CommRingCat.ofHom f) ≫
            (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
              AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) := by
  obtain ⟨j, u, g, hu, hgcoords, hgpoint⟩ :=
    exists_ambientCoordinateChartMap_of_cubicSurfaceAffinePoint p hp c x hx
  refine ⟨j, u, f.comp g, hu, ?_, ?_⟩
  · intro i
    change f (g (AllCharacteristics.GradedChart.normalized
      (MvPolynomial.homogeneousSubmodule (Fin 4) K)
      (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X K i))) = _
    rw [hgcoords]
  · calc
      Spec.map (CommRingCat.ofHom (f.comp g)) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
            (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) (by decide : 0 < 1) =
        Spec.map (CommRingCat.ofHom f) ≫
          (Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 4) K)
              (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)
                (by decide : 0 < 1)) := by
          rw [← Category.assoc, ← Spec.map_comp]
          rfl
      _ = Spec.map (CommRingCat.ofHom f) ≫
          (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
            AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) := by
          rw [hgpoint]

/-- A normalized affine point of the cubic surface is a closed projective
point. Its coordinate evaluation is surjective because constants already
recover every scalar. -/
theorem cubicSurfaceAffinePointLinearNormalizedProjectivePoint_isClosedImmersion
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    IsClosedImmersion
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx) := by
  apply linearNormalizedPoint_isClosedImmersion
  intro a
  refine ⟨MvPolynomial.C a, ?_⟩
  simp

/-- The image of the unique point of the normalized affine spectrum is a
closed point of the cubic surface. -/
theorem isClosed_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_image
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    IsClosed {(cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx)
      (IsLocalRing.closedPoint K)} := by
  letI : IsClosedImmersion
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx) :=
    cubicSurfaceAffinePointLinearNormalizedProjectivePoint_isClosedImmersion p hp c x hx
  let xK : AlgebraicGeometry.Spec (.of K) := IsLocalRing.closedPoint K
  change IsClosed {(cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx) xK}
  simpa only [Set.image_singleton] using
    (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx).isClosedMap {xK}
      isClosed_singleton

/-- A normalized marked point remains a closed immersion after passage from
the cubic surface to its ambient projective space. -/
theorem cubicSurfaceAffinePointLinearNormalizedProjectivePoint_comp_hypersurfaceToAmbient_isClosedImmersion
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) :
    IsClosedImmersion
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
        AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) := by
  letI : IsClosedImmersion
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx) :=
    cubicSurfaceAffinePointLinearNormalizedProjectivePoint_isClosedImmersion p hp c x hx
  infer_instance

/-- A residue-field-valued ambient point lying at a normalized marked cubic
surface point factors through that marked point over the same residue field. -/
theorem exists_spec_factor_cubicSurfaceAffinePointLinearNormalizedProjectivePoint_of_mem_ambient_range
    {K L : Type u} [Field K] [Field L] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (c : Fin 4 → K) (x : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0)
    (a : AlgebraicGeometry.Spec (.of L) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (ha : a (IsLocalRing.closedPoint L) ∈ Set.range
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
        AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp)) :
    ∃ b : AlgebraicGeometry.Spec (.of L) ⟶ AlgebraicGeometry.Spec (.of K),
      b ≫ cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
        AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp = a := by
  letI : IsClosedImmersion
      (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
        AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) :=
    cubicSurfaceAffinePointLinearNormalizedProjectivePoint_comp_hypersurfaceToAmbient_isClosedImmersion
      p hp c x hx
  exact (AllCharacteristics.fieldPoint_mem_closed_range_iff
    (cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≫
      AllCharacteristics.HomogeneousProjective.hypersurfaceToAmbient p hp) a).mp ha

/-- Distinct cone directions give distinct actual projective points after
normalizing them in one common linear chart. -/
theorem cubicSurfaceAffinePointLinearNormalizedProjectivePoint_ne
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (x y : cubicSurfaceAffinePoints p)
    (hx : MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0)
    (hy : MvPolynomial.aeval y.1 (homogeneousLinearForm c) ≠ 0)
    (hdir : ∀ a : K, y.1 ≠ a • x.1) :
    cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c x hx ≠
      cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c y hy := by
  intro h
  unfold cubicSurfaceAffinePointLinearNormalizedProjectivePoint at h
  dsimp only [linearNormalizedPoint] at h
  let I := AllCharacteristics.HomogeneousProjective.equationIdeal p hp
  let ell := homogeneousLinearForm c
  let z := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ AllCharacteristics.HomogeneousProjective.grading I 1 :=
    AllCharacteristics.HomogeneousProjective.polynomial_class_mem_grading I ell
      (homogeneousLinearForm_isHomogeneous c)
  let j := AlgebraicGeometry.Proj.awayι
    (AllCharacteristics.HomogeneousProjective.grading I) z hz (by decide : 0 < 1)
  change _ ≫ j = _ ≫ j at h
  have hchart := (cancel_mono j).mp h
  have hring := congrArg CommRingCat.Hom.hom (AlgebraicGeometry.Spec.map_injective hchart)
  let nx := cubicSurfaceAffinePointNormalizedConeCoordinates c x.1
  let ny := cubicSurfaceAffinePointNormalizedConeCoordinates c y.1
  have hxell : MvPolynomial.aeval nx ell = 1 := by
    exact cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval c x.1 hx
  have hyell : MvPolynomial.aeval ny ell = 1 := by
    exact cubicSurfaceAffinePointNormalizedConeCoordinates_linear_eval c y.1 hy
  have heX : ∀ q ∈ I.toIdeal, MvPolynomial.aeval nx q = 0 := by
    intro q hq
    change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    rw [hr, map_mul,
      cubicSurfaceAffinePointNormalizedConeCoordinates_surface_eval p hp c x, zero_mul]
  have heY : ∀ q ∈ I.toIdeal, MvPolynomial.aeval ny q = 0 := by
    intro q hq
    change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
    rw [hr, map_mul,
      cubicSurfaceAffinePointNormalizedConeCoordinates_surface_eval p hp c y, zero_mul]
  let gx := linearNormalizedPointChartMap I nx ell hxell heX
  let gy := linearNormalizedPointChartMap I ny ell hyell heY
  have hring' : gx = gy := by exact hring
  have hnorm : nx = ny := by
    ext k
    have hk := DFunLike.congr_fun hring'
      (linearChartCoordinate I z hz k)
    calc
      nx k = gx (linearChartCoordinate I z hz k) := by
        exact (linearNormalizedPointChartMap_coordinate I nx ell
          (homogeneousLinearForm_isHomogeneous c) hxell heX k).symm
      _ = gy (linearChartCoordinate I z hz k) := hk
      _ = ny k := by
        exact linearNormalizedPointChartMap_coordinate I ny ell
          (homogeneousLinearForm_isHomogeneous c) hyell heY k
  have hx' : MvPolynomial.eval x.1 ell ≠ 0 := by simpa [ell] using hx
  have hy' : MvPolynomial.eval y.1 ell ≠ 0 := by simpa [ell] using hy
  apply hdir ((MvPolynomial.eval y.1 ell) * (MvPolynomial.eval x.1 ell)⁻¹)
  calc
    y.1 = MvPolynomial.eval y.1 ell • ny := by
      dsimp [ny, cubicSurfaceAffinePointNormalizedConeCoordinates]
      rw [smul_smul, mul_inv_cancel₀ hy', one_smul]
    _ = MvPolynomial.eval y.1 ell • nx := by rw [hnorm]
    _ = (MvPolynomial.eval y.1 ell * (MvPolynomial.eval x.1 ell)⁻¹) • x.1 := by
      dsimp [nx, cubicSurfaceAffinePointNormalizedConeCoordinates]
      rw [smul_smul]

/-- Inserting a fresh element before a prescribed ten-element enumeration
gives an eleven-element enumeration whose successor coordinates are exactly
the original enumeration. -/
theorem exists_finElevenEquiv_insert_of_finTenEquiv
    {α : Type u} [DecidableEq α] {s : Finset α} {x : α} (hx : x ∉ s)
    (e : Fin 10 ≃ s) :
    ∃ e' : Fin 11 ≃ ↑(insert x s),
      e' 0 = ⟨x, Finset.mem_insert_self x s⟩ ∧
      ∀ j : Fin 10, e' j.succ =
        ⟨e j, Finset.mem_insert_of_mem (e j).2⟩ := by
  let f : Fin 11 → ↑(insert x s) := Fin.cons ⟨x, Finset.mem_insert_self x s⟩
    (fun k => ⟨e k, Finset.mem_insert_of_mem (e k).2⟩)
  have hfi : Function.Injective f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => rfl
      | succ k =>
        simp only [f, Fin.cons_zero, Fin.cons_succ] at hab
        apply (hx ?_).elim
        have hval : x = (e k).1 :=
          congrArg (fun z : ↑(insert x s) => z.1) hab
        exact hval.symm ▸ (e k).2
    | succ j =>
      cases b using Fin.cases with
      | zero =>
        simp only [f, Fin.cons_zero, Fin.cons_succ] at hab
        apply (hx ?_).elim
        have hval : (e j).1 = x :=
          congrArg (fun z : ↑(insert x s) => z.1) hab
        exact hval ▸ (e j).2
      | succ k =>
        simp only [f, Fin.cons_succ] at hab
        apply congrArg Fin.succ
        apply e.injective
        apply Subtype.ext
        exact congrArg (fun z : ↑(insert x s) => z.1) hab
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      exact ⟨0, by simp [f]⟩
    · obtain ⟨j, hj⟩ := e.surjective ⟨y, hy⟩
      refine ⟨j.succ, ?_⟩
      simp only [f, Fin.cons_succ]
      apply Subtype.ext
      exact congrArg (fun z : s => z.1) hj
  let e' := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e', ?_, ?_⟩
  · change f 0 = _
    simp [f]
  · intro j
    change f j.succ = _
    simp [f]

/-- A prescribed enumeration of a direction-separated finite set of cone
points determines an actual ordered configuration point of the cubic
surface.  The construction uses one common linear chart and retains the
normalized field-valued surface points as its prescribed coordinates. -/
theorem exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData_indexed
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (s : Finset (cubicSurfaceAffinePoints p)) {n : ℕ} (e : Fin n ≃ s)
    (hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1) :
    ∃ c : Fin 4 → K, ∃ hcommon : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ q : Fin n → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n).left,
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n i).left = q i := by
  obtain ⟨c, hcommon⟩ :=
    exists_common_homogeneousLinearForm_nonzero_on_cubicSurfaceAffinePoints p s
  let q : Fin n → (AlgebraicGeometry.Spec (.of K) ⟶
      AllCharacteristics.HomogeneousProjective.hypersurface p hp) :=
    fun i => cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
      (hcommon (e i).1 (e i).2)
  have hqbase : ∀ i, q i ≫
      AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    intro i
    exact cubicSurfaceAffinePointLinearNormalizedProjectivePoint_toBase p hp c (e i).1
      (hcommon (e i).1 (e i).2)
  have hqdist : ∀ i j, i ≠ j → q i ≠ q j := by
    intro i j hij
    have heq : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      apply e.injective
      exact Subtype.ext h
    exact cubicSurfaceAffinePointLinearNormalizedProjectivePoint_ne p hp c (e i).1 (e j).1
      (hcommon (e i).1 (e i).2) (hcommon (e j).1 (e j).2)
      (hsdir (e i).1 (e i).2 (e j).1 (e j).2 heq)
  obtain ⟨a, haBase, haCoordinates⟩ :=
    AllCharacteristics.exists_orderedConfigurationFieldPoint
      (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K))) q hqbase hqdist
  exact ⟨c, hcommon, q, a, fun i => rfl, haBase, haCoordinates⟩

/-- A direction-separated finite set of cone points determines an actual
point of the corresponding ordered configuration scheme of the cubic
surface.  The construction chooses an enumeration of the set. -/
theorem exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (s : Finset (cubicSurfaceAffinePoints p)) {n : ℕ} (hscard : s.card = n)
    (hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1) :
    ∃ c : Fin 4 → K, ∃ hcommon : ∀ x ∈ s,
      MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin n ≃ s,
      ∃ q : Fin n → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n).left,
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) n i).left = q i := by
  let e : Fin n ≃ s :=
    (Fintype.equivFinOfCardEq (α := s) (by simpa using hscard)).symm
  obtain ⟨c, hcommon, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData_indexed
      p hp s e hsdir
  exact ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩

/-- The concrete eight-point quadratic interpolation witness determines a
field-valued point of the ordered configuration scheme.  At that point the
full quadratic section space maps surjectively to the eight scalar values.
This is the nonemptiness witness for the independent-conditions locus used
in Voisin's degree-eight fixed-component argument. -/
theorem
    exists_eight_cubicSurfaceQuadraticIndependent_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 8 ≃ s,
      ∃ q : Fin 8 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8).left,
      s.card = 8 ∧
      Function.Surjective ((finsetEvaluation s).comp
        (cubicSurfaceCoordinatePointEvaluation p hp (d := 2))) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint
        p hp c (e i).1 (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8 i).left = q i := by
  obtain ⟨s, hscard, hsurj, hsdir⟩ :=
    exists_eight_cubicSurfaceCoordinatePoint_evaluation_surjective
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hsurj, hq, haBase, haCoordinates⟩

/-- Ten direction-separated points with invertible quadratic evaluation give
an actual ordered ten-point configuration of the cubic surface.  Over every
coefficient-field extension, its marked points detect every homogeneous form
of degree at most two. -/
theorem exists_ten_cubicSurfaceLowDegreeAvoidance_orderedConfigurationFieldPoint_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 10 ≃ s,
      ∃ q : Fin 10 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 10).left,
      s.card = 10 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) {d : ℕ}, d ≤ 2 →
        ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous d →
          (∀ z ∈ s, MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 10).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 10)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 10 i).left = q i := by
  obtain ⟨s, hscard, hbij, hsdir⟩ :=
    exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  refine ⟨s, c, hcommon, e, q, a, hscard, ?_, hq, haBase, haCoordinates⟩
  intro L _ f d hd r hr hvan
  apply homogeneous_of_le_two_of_quadratic_avoidance s
    (fun z i => f (z.1 i)) ?_ hd r hr hvan
  intro q hq hqvan
  exact quadraticAvoidance_fieldExtension_of_bijective f p s hscard hbij q hq hqvan

/-- The ten-point quadratic-interpolation tuple extends by one fresh
projective direction to an eleven-point configuration.  After deleting its
zeroth coordinate, the remaining ordered points still detect every
homogeneous form of degree at most two over every coefficient-field
extension. -/
theorem exists_eleven_cubicSurfaceSuccessorLowDegreeAvoidance_orderedConfigurationFieldPoint_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ S : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ S,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ S,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      (∀ {L : Type u} [Field L] (f : K →+* L) {d : ℕ}, d ≤ 2 →
        ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous d →
          (∀ j : Fin 10,
            MvPolynomial.aeval (fun i => f (((e (Fin.succ j)).1.1) i)) r = 0) → r = 0) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  classical
  obtain ⟨s, hscard, hbij, hsdir⟩ :=
    exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
      p hp hne hprime
  obtain ⟨t, htcard, htbij⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective p hp hne hprime
  have htdir : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → ∀ a : K, v.1 ≠ a • u.1 := by
    intro u hu v hv huv a
    exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
      p hp t htbij hu hv huv a
  have hstlt : s.card < t.card := by omega
  obtain ⟨x, hxt, hxdir⟩ :=
    exists_cubicSurfaceAffinePoint_direction_outside_of_card_lt p s t hstlt htdir
  have hxnot : x ∉ s := by
    intro hxs
    exact (hxdir x hxs 1) (by simp)
  let e : Fin 10 ≃ s :=
    (Fintype.equivFinOfCardEq (α := s) (by simpa using hscard)).symm
  obtain ⟨e', hezero, hesucc⟩ := exists_finElevenEquiv_insert_of_finTenEquiv hxnot e
  have hSdir : ∀ u ∈ insert x s, ∀ v ∈ insert x s, u ≠ v →
      ∀ a : K, v.1 ≠ a • u.1 := by
    intro u hu v hv huv a
    rcases Finset.mem_insert.mp hu with hux | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact (huv rfl).elim
      · exact not_smul_symm_of_nonzero x.1 v.1 v.2.2 (hxdir v hv) a
    · rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact hxdir u hu a
      · exact hsdir u hu v hv huv a
  obtain ⟨c, hcommon, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData_indexed
      p hp (insert x s) e' hSdir
  refine ⟨insert x s, c, hcommon, e', q, a, ?_, hq, haBase, haCoordinates⟩
  intro L _ f d hd r hr hvan
  apply homogeneous_of_le_two_of_quadratic_avoidance s
    (fun z i => f (z.1 i)) ?_ hd r hr ?_
  · intro q hq hqvan
    exact quadraticAvoidance_fieldExtension_of_bijective f p s hscard hbij q hq hqvan
  · intro z hz
    obtain ⟨j, hj⟩ := e.surjective ⟨z, hz⟩
    have hpoint : (e' j.succ).1 = z := by
      have hpoint' := congrArg Subtype.val (hesucc j)
      simpa only [hj] using hpoint'
    simpa only [hpoint] using hvan j

/-- Pulling the universal union of the eleven ordered coordinate sections to
a field-valued configuration point gives its actual finite flat subscheme on
the corresponding cubic-surface fiber. -/
noncomputable def cubicSurfaceOrderedConfigurationFiberFiniteSubscheme
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (a : AlgebraicGeometry.Spec (.of K) ⟶
      (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left) :
    AllCharacteristics.FiniteSubschemeDatum
      (pullback.snd
        (pullback.snd
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
          (AllCharacteristics.orderedFamilyConfigurationOver
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a) 11 :=
  AllCharacteristics.FiniteSubschemeDatum.baseChange
    (pullback.fst
      (pullback.snd
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a)
    a
    (IsPullback.of_hasPullback _ _)
    (AllCharacteristics.orderedConfigurationFiniteSubscheme
      (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)

/-- The finite subscheme obtained from an ordered eleven-point configuration
has the prescribed constant rank eleven. -/
theorem cubicSurfaceOrderedConfigurationFiberFiniteSubscheme_rank
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (a : AlgebraicGeometry.Spec (.of K) ⟶
      (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left) :
    let f := pullback.snd
      (pullback.snd
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a
    let D := cubicSurfaceOrderedConfigurationFiberFiniteSubscheme p hp a
    letI : AlgebraicGeometry.IsFinite (D.val.subschemeι ≫ f) := D.property.1
    AllCharacteristics.finiteSchemeRank (D.val.subschemeι ≫ f) = 11 := by
  let f := pullback.snd
    (pullback.snd
      (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
      (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a
  let D := cubicSurfaceOrderedConfigurationFiberFiniteSubscheme p hp a
  letI : AlgebraicGeometry.IsFinite (D.val.subschemeι ≫ f) := D.property.1
  exact AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank f D

/-- The finite subscheme at an actual ordered configuration point is étale
over its field-valued base.  In particular, the concrete eleven-point datum
is reduced as required for the residual constructions. -/
theorem cubicSurfaceOrderedConfigurationFiberFiniteSubscheme_toBase_etale
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (a : AlgebraicGeometry.Spec (.of K) ⟶
      (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left) :
    Etale ((cubicSurfaceOrderedConfigurationFiberFiniteSubscheme p hp a).val.subschemeι ≫
      pullback.snd
        (pullback.snd
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
          (AllCharacteristics.orderedFamilyConfigurationOver
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a) := by
  let F := AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp
  let C := (AllCharacteristics.orderedFamilyConfigurationOver F 11).left
  let q : pullback F (AllCharacteristics.orderedFamilyConfigurationOver F 11).hom ⟶ C :=
    pullback.snd F (AllCharacteristics.orderedFamilyConfigurationOver F 11).hom
  let g : pullback q a ⟶ pullback F (AllCharacteristics.orderedFamilyConfigurationOver F 11).hom :=
    pullback.fst q a
  let h : IsPullback g (pullback.snd q a) q a := IsPullback.of_hasPullback q a
  let D := AllCharacteristics.orderedConfigurationFiniteSubscheme F 11
  letI : Etale (D.val.subschemeι ≫ q) := by
    change Etale ((AllCharacteristics.orderedConfigurationFiniteSubscheme F 11).val.subschemeι ≫
      pullback.snd F (AllCharacteristics.orderedFamilyConfigurationOver F 11).hom)
    exact AllCharacteristics.orderedConfigurationFiniteSubscheme_toBase_etale F 11
  change Etale ((AllCharacteristics.FiniteSubschemeDatum.baseChange g a h D).val.subschemeι ≫
    pullback.snd q a)
  exact AllCharacteristics.FiniteSubschemeDatum.baseChange_toBase_etale g a h D

/-- There is a concrete length-eleven configuration of nonzero affine-cone
points on a prime cubic surface on which no nonzero quadratic form vanishes.
This is the point-configuration counterpart of the strict quadratic-section
inequality in Voisin's degree-ten argument. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 11 ∧
      ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
        (∀ x ∈ s, MvPolynomial.aeval x.1 q = 0) → q = 0 := by
  classical
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_ten_cubicSurfaceAffinePoint_quadratic_evaluation_bijective
      p hp hne hprime
  obtain ⟨t, htcard, _⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have hnotle : ¬ t ⊆ s := by
    intro hle
    have hcardle := Finset.card_le_card hle
    omega
  obtain ⟨x, hxt, hxnot⟩ := Finset.not_subset.mp hnotle
  refine ⟨insert x s, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxnot, hscard]
  · intro q hq hvan
    let q' : MvPolynomial.homogeneousSubmodule (Fin 4) K 2 := ⟨q, hq⟩
    have hzero : ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p
          (MvPolynomial.homogeneousSubmodule (Fin 4) K 2))) q' = 0 := by
      ext y
      change MvPolynomial.aeval y.1.1 q = 0
      apply hvan y
      exact Finset.mem_insert_of_mem y.2
    have hqzero : q' = 0 := hsbij.1 (by
      rw [hzero, map_zero])
    exact congrArg Subtype.val hqzero

/-- On a prime cubic surface, one can choose eleven nonzero affine-cone points
with the quadratic Cayley--Bacharach property: after removing any one point,
the remaining ten still detect every quadratic form.  The eleventh point is
chosen outside the product of the ten deletion quadrics, so each deletion
kernel is killed by evaluation there. -/
theorem exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ S : Finset (cubicSurfaceAffinePoints p), S.card = 11 ∧
      (∀ y ∈ S, ∀ r : MvPolynomial (Fin 4) K, r.IsHomogeneous 2 →
        (∀ z ∈ S, z ≠ y → MvPolynomial.aeval z.1 r = 0) → r = 0) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  classical
  obtain ⟨s, hscard, hsbij, hsdir⟩ :=
    exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
      p hp hne hprime
  let W := MvPolynomial.homogeneousSubmodule (Fin 4) K 2
  let ev : W →ₗ[K] (cubicSurfaceAffinePoints p → K) :=
    cubicSurfacePointEvaluation p W
  have hsbij' : Function.Bijective ((finsetEvaluation s).comp ev) := by
    simpa only [W, ev] using hsbij
  have hWdim : Module.finrank K W = 10 := by
    dsimp only [W]
    rw [four_variable_homogeneous_finrank]
    decide
  have hkernel : ∀ y : s, ∃ q : W, q ≠ 0 ∧
      ((finsetEvaluation (s.erase y.1)).comp ev) q = 0 := by
    intro y
    by_contra h
    have hker : LinearMap.ker ((finsetEvaluation (s.erase y.1)).comp ev) = ⊥ := by
      apply LinearMap.ker_eq_bot.mpr
      apply (injective_iff_map_eq_zero _).mpr
      intro q hq
      by_contra hq0
      exact h ⟨q, hq0, hq⟩
    have hinj : Function.Injective ((finsetEvaluation (s.erase y.1)).comp ev) :=
      LinearMap.ker_eq_bot.mp hker
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hy : y.1 ∈ s := y.2
    have hcarderase : (s.erase y.1).card = 9 := by
      rw [Finset.card_erase_of_mem hy, hscard]
    rw [hWdim, Module.finrank_pi_fintype] at hle
    have hle' : 10 ≤ (s.erase y.1).card := by
      simpa [Module.finrank_self, Fintype.card_coe] using hle
    omega
  choose q hqne hqvan using hkernel
  have hqnot : ∀ y : s, (q y).1 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro y hqmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hqmem
    have hrp : r * p = (q y).1 := by
      rw [mul_comm]
      exact hr.symm
    have hrzero : r = 0 := eq_zero_of_mul_homogeneous_lt hp hne (by
      rw [hrp]
      exact (q y).2) (by decide)
    apply hqne y
    have hqzero : (q y).1 = 0 := by
      rw [← hrp, hrzero, zero_mul]
    apply Subtype.ext
    simpa using hqzero
  let Q : MvPolynomial (Fin 4) K := ∏ y : s, (q y).1
  have hQhom : Q.IsHomogeneous (∑ _ : s, 2) := by
    dsimp only [Q]
    exact MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset s)
      (fun y => (q y).1) (fun _ => 2) (fun y _ => (q y).2)
  have hQnot : Q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro hQmem
    have hfactor : ∃ y ∈ (Finset.univ : Finset s),
        (q y).1 ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
      rw [← Ideal.IsPrime.prod_mem_iff]
      simpa only [Q] using hQmem
    obtain ⟨y, -, hy⟩ := hfactor
    exact hqnot y hy
  have hQpos : 0 < ∑ _ : s, 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hscard]
    norm_num
  obtain ⟨x, hxne, hxzero, hxQ⟩ :=
    exists_cubicSurfaceAffinePoint_eval_ne_zero_of_not_mem_span p Q hQhom hQpos
      hprime hQnot
  let x' : cubicSurfaceAffinePoints p := ⟨x, hxzero, hxne⟩
  have hxq : ∀ y : s, MvPolynomial.aeval x (q y).1 ≠ 0 := by
    intro y hzero
    apply hxQ
    dsimp only [Q]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ y) hzero
  have hQzero : ∀ y : s, MvPolynomial.aeval y.1.1 Q = 0 := by
    intro y
    have herasecard : (s.erase y.1).card = 9 := by
      rw [Finset.card_erase_of_mem y.2, hscard]
    obtain ⟨z, hz⟩ : (s.erase y.1).Nonempty :=
      Finset.card_pos.mp (by omega)
    let z' : s := ⟨z, (Finset.mem_erase.mp hz).2⟩
    have hzero := congrFun (hqvan z')
      ⟨y.1, Finset.mem_erase.mpr
        ⟨fun hyz => (Finset.mem_erase.mp hz).1 hyz.symm, y.2⟩⟩
    change MvPolynomial.aeval y.1.1 (q z').1 = 0 at hzero
    dsimp only [Q]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ z') hzero
  have hxnot : x' ∉ s := by
    intro hxs
    have herasecard : (s.erase x').card = 9 := by
      rw [Finset.card_erase_of_mem hxs, hscard]
    obtain ⟨z, hz⟩ : (s.erase x').Nonempty :=
      Finset.card_pos.mp (by omega)
    let y : s := ⟨x', hxs⟩
    let z' : s := ⟨z, (Finset.mem_erase.mp hz).2⟩
    have hzy : x' ≠ z' := by
      intro hxz
      have : x' = z := by simpa only [z'] using hxz
      exact (Finset.mem_erase.mp hz).1 this.symm
    have hzero := congrFun (hqvan z')
      ⟨x', Finset.mem_erase.mpr ⟨hzy, hxs⟩⟩
    change MvPolynomial.aeval x (q z').1 = 0 at hzero
    exact hxq z' hzero
  have hxdir : ∀ y ∈ s, ∀ a : K, x'.1 ≠ a • y.1 := by
    intro y hy a hxy
    apply hxQ
    have hxy' : x = a • y.1 := by
      simpa only [x'] using hxy
    rw [hxy', aeval_smul_of_isHomogeneous Q hQhom,
      hQzero ⟨y, hy⟩, mul_zero]
  refine ⟨insert x' s, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxnot, hscard]
  · intro y hy r hr hvan
    let r' : W := ⟨r, hr⟩
    rcases Finset.mem_insert.mp hy with hyx | hys
    · subst y
      have hrzero : ((finsetEvaluation s).comp ev) r' = 0 := by
        ext z
        change MvPolynomial.aeval z.1.1 r = 0
        apply hvan z (Finset.mem_insert_of_mem z.2)
        intro hzx
        apply hxnot
        simpa only [hzx] using z.2
      have hr'zero : r' = 0 := hsbij'.1 (by rw [hrzero, map_zero])
      exact congrArg Subtype.val hr'zero
    · have hqy : MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1 ≠ 0 := by
        intro hqzero
        apply hqne ⟨y, hys⟩
        apply hsbij'.1
        ext z
        change MvPolynomial.aeval z.1.1 (q ⟨y, hys⟩).1 = 0
        by_cases hzy : z.1 = y
        · simpa only [hzy] using hqzero
        · have hzero := congrFun (hqvan ⟨y, hys⟩)
            ⟨z.1, Finset.mem_erase.mpr ⟨hzy, z.2⟩⟩
          change MvPolynomial.aeval z.1.1 (q ⟨y, hys⟩).1 = 0 at hzero
          exact hzero
      have hrscalar : r' =
          (MvPolynomial.aeval y.1 r / MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1) •
            q ⟨y, hys⟩ := by
        apply hsbij'.1
        ext z
        change MvPolynomial.aeval z.1.1 r =
          MvPolynomial.aeval z.1.1
            (((MvPolynomial.aeval y.1 r /
              MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1) • q ⟨y, hys⟩).1)
        by_cases hzy : z.1 = y
        · have hvaluey : MvPolynomial.aeval y.1 r =
            MvPolynomial.aeval y.1 (((MvPolynomial.aeval y.1 r /
              MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1) •
              q ⟨y, hys⟩).1)
            := by
              rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul,
                MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
              exact (div_mul_cancel₀ _ hqy).symm
          simpa only [hzy] using hvaluey
        · have hrzero := hvan z (Finset.mem_insert_of_mem z.2) (fun h => hzy h)
          have hqzero := congrFun (hqvan ⟨y, hys⟩)
            ⟨z.1, Finset.mem_erase.mpr ⟨hzy, z.2⟩⟩
          change MvPolynomial.aeval z.1.1 (q ⟨y, hys⟩).1 = 0 at hqzero
          rw [hrzero]
          change 0 = MvPolynomial.aeval z.1.1
            (((MvPolynomial.aeval y.1 r /
              MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1) •
              (q ⟨y, hys⟩).1))
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.aeval_C,
            Algebra.algebraMap_self, RingHom.id_apply, hqzero, mul_zero]
      have hrx : MvPolynomial.aeval x r = 0 := by
        exact hvan x' (Finset.mem_insert_self x' s) (fun hxy => hxnot (hxy ▸ hys))
      have hrscalarx := congrArg (fun v : W => MvPolynomial.aeval x v.1) hrscalar
      change MvPolynomial.aeval x r =
        MvPolynomial.aeval x
          (((MvPolynomial.aeval y.1 r /
            MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1) • q ⟨y, hys⟩).1) at hrscalarx
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply] at hrscalarx
      have hscalarzero :
          MvPolynomial.aeval y.1 r /
              MvPolynomial.aeval y.1 (q ⟨y, hys⟩).1 = 0 := by
        apply (mul_eq_zero.mp (hrscalarx ▸ hrx)).resolve_right
        exact hxq ⟨y, hys⟩
      have hr'zero : r' = 0 := by
        rw [hrscalar, hscalarzero, zero_smul]
      exact congrArg Subtype.val hr'zero
  · intro u hu v hv huv a
    rcases Finset.mem_insert.mp hu with hux | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact (huv rfl).elim
      · exact not_smul_symm_of_nonzero x'.1 v.1 v.2.2 (hxdir v hv) a
    · rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact hxdir u hu a
      · exact hsdir u hu v hv huv a

/-- The quadratic Cayley--Bacharach property remains true after arbitrary
extension of the coefficient field.  Each deleted ten-point configuration has
a square, injective quadratic evaluation map over the original field, hence
an invertible evaluation matrix after scalar extension. -/
theorem exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ S : Finset (cubicSurfaceAffinePoints p), S.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) (y : cubicSurfaceAffinePoints p), y ∈ S →
        ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous 2 →
          (∀ z ∈ S, z ≠ y → MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  classical
  obtain ⟨S, hScard, hCB, hdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach
      p hp hne hprime
  refine ⟨S, hScard, ?_, hdir⟩
  intro L _ f y hy r hr hvan
  let T := S.erase y
  have hTcard : T.card = 10 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem hy, hScard]
  let W := MvPolynomial.homogeneousSubmodule (Fin 4) K 2
  let ev : W →ₗ[K] (cubicSurfaceAffinePoints p → K) :=
    cubicSurfacePointEvaluation p W
  have hTinjection : Function.Injective ((finsetEvaluation T).comp ev) := by
    apply finset_cubicSurfacePointEvaluation_injective_of_no_vanishing p T
    intro q hq hqvan
    apply hCB y hy q hq
    intro z hz hzy
    apply hqvan z
    exact Finset.mem_erase.mpr ⟨hzy, hz⟩
  have hWdim : Module.finrank K W = 10 := by
    dsimp only [W]
    rw [four_variable_homogeneous_finrank]
    decide
  have hdim : Module.finrank K W = Module.finrank K (T → K) := by
    rw [hWdim, Module.finrank_pi_fintype]
    simpa [Module.finrank_self, Fintype.card_coe] using hTcard.symm
  have hTbij : Function.Bijective ((finsetEvaluation T).comp ev) := by
    refine ⟨hTinjection, ?_⟩
    exact (LinearEquiv.ofInjectiveOfFinrankEq _ hTinjection hdim).surjective
  apply quadraticAvoidance_fieldExtension_of_bijective f p T hTcard
    (by simpa only [W, ev] using hTbij) r hr
  intro z hz
  exact hvan z (Finset.mem_erase.mp hz).2 (Finset.mem_erase.mp hz).1

/-- After every coefficient-field extension, deleting any one point of the
eleven-point witness detects all homogeneous forms of degree at most two.
The degree-two statement is the square interpolation result; lower degrees
are promoted by multiplying by a coordinate variable. -/
theorem exists_eleven_cubicSurfaceAffinePoints_lowDegree_cayley_bacharach_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ S : Finset (cubicSurfaceAffinePoints p), S.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) (y : cubicSurfaceAffinePoints p), y ∈ S →
        ∀ {d : ℕ}, d ≤ 2 → ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous d →
          (∀ z ∈ S, z ≠ y → MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨S, hScard, hCB, hdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach_fieldExtension
      p hp hne hprime
  refine ⟨S, hScard, ?_, hdir⟩
  intro L _ f y hy d hd r hr hvan
  exact homogeneous_of_le_two_of_quadratic_cayley_bacharach S
    (fun z i => f (z.1 i)) (hCB f) y hy hd r hr hvan

/-- The eleven-point quadratic witness remains a witness after any field
extension.  The points themselves stay indexed over the original field, while
their coordinates are transported along the field homomorphism. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_fieldExtension
    {K L : Type u} [Field K] [Field L] [IsAlgClosed K]
    (f : K →+* L) (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 11 ∧
      ∀ q : MvPolynomial (Fin 4) L, q.IsHomogeneous 2 →
        (∀ x ∈ s, MvPolynomial.aeval (fun i => f (x.1 i)) q = 0) → q = 0 := by
  classical
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_ten_cubicSurfaceAffinePoint_quadratic_evaluation_bijective
      p hp hne hprime
  obtain ⟨t, htcard, _⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have hnotle : ¬ t ⊆ s := by
    intro hle
    have hcardle := Finset.card_le_card hle
    omega
  obtain ⟨x, hxt, hxnot⟩ := Finset.not_subset.mp hnotle
  refine ⟨insert x s, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxnot, hscard]
  · intro q hq hvan
    exact quadraticAvoidance_fieldExtension_of_bijective f p s hscard hsbij q hq
      (fun y hy => hvan y (Finset.mem_insert_of_mem hy))

/-- After a field extension, the same eleven-point configuration detects all
homogeneous forms of degree at most two. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_homogeneous_of_degree_le_two_fieldExtension
    {K L : Type u} [Field K] [Field L] [IsAlgClosed K]
    (f : K →+* L) (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 11 ∧
      ∀ (e : ℕ), e ≤ 2 → ∀ q : MvPolynomial (Fin 4) L, q.IsHomogeneous e →
        (∀ x ∈ s, MvPolynomial.aeval (fun i => f (x.1 i)) q = 0) → q = 0 := by
  obtain ⟨s, hscard, hquad⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_fieldExtension
      f p hp hne hprime
  refine ⟨s, hscard, ?_⟩
  intro e he q hq hvan
  exact homogeneous_of_le_two_of_quadratic_avoidance s
    (fun x i => f (x.1 i)) hquad he q hq hvan

/-- The quadratic-avoidance configuration can moreover be chosen in eleven
distinct projective directions.  The extra direction is selected from the
nineteen-point cubic interpolation set, whose coordinate-ring evaluations
also separate scalar multiples. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 11 ∧
      (∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 2 →
        (∀ x ∈ s, MvPolynomial.aeval x.1 q = 0) → q = 0) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  classical
  obtain ⟨s, hscard, hsbij, hsdir⟩ :=
    exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
      p hp hne hprime
  obtain ⟨t, htcard, htbij⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro u hu v hv huv a
    exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
      p hp t htbij hu hv huv a
  have hstlt : s.card < t.card := by omega
  obtain ⟨x, hxt, hxdir⟩ :=
    exists_cubicSurfaceAffinePoint_direction_outside_of_card_lt p s t hstlt htdir
  have hxnot : x ∉ s := by
    intro hxs
    exact (hxdir x hxs 1) (by simp)
  refine ⟨insert x s, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxnot, hscard]
  · intro q hq hvan
    let q' : MvPolynomial.homogeneousSubmodule (Fin 4) K 2 := ⟨q, hq⟩
    have hzero : ((finsetEvaluation s).comp
        (cubicSurfacePointEvaluation p
          (MvPolynomial.homogeneousSubmodule (Fin 4) K 2))) q' = 0 := by
      ext y
      change MvPolynomial.aeval y.1.1 q = 0
      apply hvan y
      exact Finset.mem_insert_of_mem y.2
    have hqzero : q' = 0 := hsbij.1 (by
      rw [hzero, map_zero])
    exact congrArg Subtype.val hqzero
  · intro u hu v hv huv a
    rcases Finset.mem_insert.mp hu with hux | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact (huv rfl).elim
      · exact not_smul_symm_of_nonzero x.1 v.1 v.2.2 (hxdir v hv) a
    · rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact hxdir u hu a
      · exact hsdir u hu v hv huv a

/-- Every positive-degree finite-dimensional subsystem of the cubic surface's
graded coordinate ring of dimension at most eleven is detected on eleven
distinct projective directions.  This is the version used for cubic systems
modulo the defining equation. -/
theorem exists_eleven_cubicSurfaceAffinePoints_coordinateSubmodule_evaluation_injective_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 11) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 11 ∧
      Function.Injective ((finsetEvaluation u).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_bijective
      p hp hd hprime W
  have hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceCoordinateSubmodulePointEvaluation_bijective_no_smul
      p hp W s hsbij hx hy hxy a
  obtain ⟨t, htcard, _, htdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions
      p hp hne hprime
  obtain ⟨u, hsu, hucard, hudir⟩ :=
    exists_cubicSurfaceAffinePoint_directionSeparated_superset_of_card_le
      p s t (by rw [hscard, htcard]; exact hdim) hsdir htdir
  refine ⟨u, ?_, ?_, hudir⟩
  · calc
      u.card = t.card := hucard
      _ = 11 := htcard
  · exact finsetEvaluation_injective_of_subset
      ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W) hsu hsbij.1

/-- Every fixed homogeneous subsystem of a prime cubic surface has a
projectively distinct eleven-point configuration on which evaluation has
maximal rank.  This combines the existing injective witness with the
surjective witness for systems of dimension at least eleven. -/
theorem exists_eleven_cubicSurfaceCoordinateSubmodule_maximalRank_evaluation
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W] :
    ∃ t : Finset (cubicSurfaceAffinePoints p), t.card = 11 ∧
      (Function.Surjective ((finsetEvaluation t).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∨
       Function.Injective ((finsetEvaluation t).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W))) ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K,
        y.1 ≠ a • x.1 := by
  by_cases hdim : Module.finrank K W ≤ 11
  · obtain ⟨t, ht, hinj, hdir⟩ :=
      exists_eleven_cubicSurfaceAffinePoints_coordinateSubmodule_evaluation_injective_independent_directions
        p hp hne hprime hd W hdim
    exact ⟨t, ht, Or.inr hinj, hdir⟩
  · have hn : 11 ≤ Module.finrank K W := by omega
    obtain ⟨t, ht, hsurj, hdir⟩ :=
      exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_surjective
        p hp hd hprime W 11 hn
    exact ⟨t, ht, Or.inl hsurj, hdir⟩

/-- Every positive-degree finite-dimensional homogeneous section system on a
prime cubic surface whose full cone evaluation is faithful admits eleven
distinct projective directions on which its evaluation remains injective.
This is the finite-point witness needed to impose independent conditions on
an arbitrary small projective subsystem, rather than only on the full
quadratic system. -/
theorem exists_eleven_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 11) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 11 ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_cubicSurfaceAffinePoint_finset_evaluation_bijective
      p hd hprime W hhom hseparate
  have hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceAffinePointEvaluation_bijective_no_smul_of_homogeneous
      p W hhom s hsbij hx hy hxy a
  obtain ⟨t, htcard, _, htdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions
      p hp hne hprime
  obtain ⟨u, hsu, hucard, hudir⟩ :=
    exists_cubicSurfaceAffinePoint_directionSeparated_superset_of_card_le
      p s t (by rw [hscard, htcard]; exact hdim) hsdir htdir
  refine ⟨u, ?_, ?_, hudir⟩
  · calc
      u.card = t.card := hucard
      _ = 11 := htcard
  · exact finsetEvaluation_injective_of_subset
      (cubicSurfacePointEvaluation p W) hsu hsbij.1

/-- An independently evaluable homogeneous system can be enlarged from a
square interpolation set to the cardinality of any given direction-separated
configuration.  This separates the interpolation argument from the particular
number of marked points used later in a configuration space. -/
theorem exists_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions_of_target
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (t : Finset (cubicSurfaceAffinePoints p))
    (htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1)
    (hdim : Module.finrank K W ≤ t.card) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = t.card ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_cubicSurfaceAffinePoint_finset_evaluation_bijective
      p hd hprime W hhom hseparate
  have hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceAffinePointEvaluation_bijective_no_smul_of_homogeneous
      p W hhom s hsbij hx hy hxy a
  obtain ⟨u, hsu, hucard, hudir⟩ :=
    exists_cubicSurfaceAffinePoint_directionSeparated_superset_of_card_le
      p s t (by rw [hscard]; exact hdim) hsdir htdir
  exact ⟨u, hucard,
    finsetEvaluation_injective_of_subset
      (cubicSurfacePointEvaluation p W) hsu hsbij.1, hudir⟩

/-- Every positive-degree homogeneous section system of dimension at most
eight on a prime cubic surface is detected on eight distinct projective
directions.  The ambient eight-point set comes from the quadratic
interpolation witness, so this is the exact length needed in `leeffective`. -/
theorem exists_eight_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 8) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 8 ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨t, htcard, _, htdir⟩ :=
    exists_eight_cubicSurfaceCoordinatePoint_evaluation_surjective
      p hp hne hprime
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions_of_target
      p hd hprime W hhom hseparate t htdir (by rw [htcard]; exact hdim)
  exact ⟨u, hucard.trans htcard, huinj, hudir⟩

/-- The eight-point evaluator for an arbitrary small homogeneous system is
realized by a field-valued point of the ordered configuration scheme. -/
theorem exists_eight_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 8) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ u,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 8 ≃ u,
      ∃ q : Fin 8 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8).left,
      u.card = 8 ∧
        Function.Injective ((finsetEvaluation u).comp
          (cubicSurfacePointEvaluation p W)) ∧
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
        (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint
          p hp c (e i).1 (hcommon (e i).1 (e i).2)) ∧
        a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8).hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 8 i).left = q i := by
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_eight_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
      p hp hne hprime hd W hhom hseparate hdim
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp u hucard hudir
  exact ⟨u, c, hcommon, e, q, a, hucard, huinj, hudir,
    hq, haBase, haCoordinates⟩

/-- Every positive-degree homogeneous section system of dimension at most
sixteen on a prime cubic surface is detected on sixteen distinct projective
directions.  The ambient direction set is cut from the nineteen-point cubic
interpolation set, so the result is available at the length used in Voisin's
first cubic--cubic residual construction. -/
theorem exists_sixteen_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 16) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 16 ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
      p hp s hsbij hx hy hxy a
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := s) (by
    rw [hscard]
    omega : 16 ≤ s.card)
  have htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact hsdir x (hts hx) y (hts hy) hxy a
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions_of_target
      p hd hprime W hhom hseparate t htdir (by rw [htcard]; exact hdim)
  exact ⟨u, hucard.trans htcard, huinj, hudir⟩

/-- The sixteen-point interpolation witness for a homogeneous system is an
actual ordered configuration point of the cubic surface.  This is the
configuration length of the completed degree-ten datum in Voisin's first
residual step. -/
theorem exists_sixteen_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 16) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ u,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 16 ≃ u,
      ∃ q : Fin 16 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16).left,
      u.card = 16 ∧
        Function.Injective ((finsetEvaluation u).comp
          (cubicSurfacePointEvaluation p W)) ∧
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
        (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
          (hcommon (e i).1 (e i).2)) ∧
        a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16).hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16 i).left = q i := by
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_sixteen_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
      p hp hne hprime hd W hhom hseparate hdim
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp u hucard hudir
  exact ⟨u, c, hcommon, e, q, a, hucard, huinj, hudir,
    hq, haBase, haCoordinates⟩

/-- Every positive-degree finite-dimensional subsystem of the cubic surface's
graded coordinate ring of dimension at most sixteen is detected on sixteen
distinct projective directions.  This is the intrinsic coordinate-ring form
of the length used by the degree-ten completion. -/
theorem exists_sixteen_cubicSurfaceAffinePoints_coordinateSubmodule_evaluation_injective_independent_directions
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 16) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 16 ∧
      Function.Injective ((finsetEvaluation u).comp
        ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  obtain ⟨s, hscard, hsbij⟩ :=
    exists_cubicSurfaceCoordinateSubmodule_finset_evaluation_bijective
      p hp hd hprime W
  have hsdir : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceCoordinateSubmodulePointEvaluation_bijective_no_smul
      p hp W s hsbij hx hy hxy a
  obtain ⟨t, htcard, htbij⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
      p hp t htbij hx hy hxy a
  obtain ⟨v, hvt, hvcard⟩ := Finset.exists_subset_card_eq (s := t) (by
    rw [htcard]
    omega : 16 ≤ t.card)
  have hvdir : ∀ x ∈ v, ∀ y ∈ v, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro x hx y hy hxy a
    exact htdir x (hvt hx) y (hvt hy) hxy a
  obtain ⟨u, hsu, hucard, hudir⟩ :=
    exists_cubicSurfaceAffinePoint_directionSeparated_superset_of_card_le
      p s v (by rw [hscard, hvcard]; exact hdim) hsdir hvdir
  refine ⟨u, hucard.trans hvcard, ?_, hudir⟩
  exact finsetEvaluation_injective_of_subset
    ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W) hsu hsbij.1

/-- The intrinsic sixteen-point graded-coordinate interpolation witness is
realized by an actual ordered configuration point of the cubic surface. -/
theorem exists_sixteen_cubicSurfaceCoordinateSubmodule_evaluation_injective_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 16) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ u,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 16 ≃ u,
      ∃ q : Fin 16 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16).left,
      u.card = 16 ∧
        Function.Injective ((finsetEvaluation u).comp
          ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∧
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
        (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
          (hcommon (e i).1 (e i).2)) ∧
        a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16).hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 16 i).left = q i := by
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_sixteen_cubicSurfaceAffinePoints_coordinateSubmodule_evaluation_injective_independent_directions
      p hp hne hprime hd W hdim
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp u hucard hudir
  exact ⟨u, c, hcommon, e, q, a, hucard, huinj, hudir,
    hq, haBase, haCoordinates⟩

/-- The eleven-point interpolation witness for an arbitrary homogeneous
system can be realized as an actual ordered configuration point of the cubic
surface.  It retains the common normalization chart and the distinct
projective directions needed by the projective-incidence argument. -/
theorem exists_eleven_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ q ∈ W, q.IsHomogeneous d)
    (hseparate : ∀ q ∈ W,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0)
    (hdim : Module.finrank K W ≤ 11) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ u,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ u,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      u.card = 11 ∧
        Function.Injective ((finsetEvaluation u).comp
          (cubicSurfacePointEvaluation p W)) ∧
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
        (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
          (hcommon (e i).1 (e i).2)) ∧
        a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
      p hp hne hprime hd W hhom hseparate hdim
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp u hucard hudir
  exact ⟨u, c, hcommon, e, q, a, hucard, huinj, hudir,
    hq, haBase, haCoordinates⟩

/-- The eleven-point interpolation witness for a finite-dimensional graded
coordinate-ring subsystem is likewise an actual ordered cubic-surface
configuration.  In particular, this packages degree-three systems modulo
the defining cubic in the same geometric form as the polynomial-system
witness. -/
theorem exists_eleven_cubicSurfaceCoordinateSubmodule_evaluation_injective_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d : ℕ} (hd : 0 < d)
    (W : Submodule K
      (AllCharacteristics.HomogeneousProjective.grading
        (AllCharacteristics.HomogeneousProjective.equationIdeal p hp) d))
    [FiniteDimensional K W]
    (hdim : Module.finrank K W ≤ 11) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ u,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ u,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      u.card = 11 ∧
        Function.Injective ((finsetEvaluation u).comp
          ((cubicSurfaceCoordinatePointEvaluation p hp (d := d)).domRestrict W)) ∧
        (∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
        (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
          (hcommon (e i).1 (e i).2)) ∧
        a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨u, hucard, huinj, hudir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_coordinateSubmodule_evaluation_injective_independent_directions
      p hp hne hprime hd W hdim
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp u hucard hudir
  exact ⟨u, c, hcommon, e, q, a, hucard, huinj, hudir,
    hq, haBase, haCoordinates⟩

/-- The direction-separated eleven-point quadratic witness can be chosen
extension-stably: every scalar extension still detects a nonzero quadric on
the same eleven cone points. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), s.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L)
        (q : MvPolynomial (Fin 4) L), q.IsHomogeneous 2 →
          (∀ x ∈ s, MvPolynomial.aeval (fun i ↦ f (x.1 i)) q = 0) → q = 0) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  classical
  obtain ⟨s, hscard, hsbij, hsdir⟩ :=
    exists_ten_cubicSurfaceAffinePoints_quadratic_independent_directions
      p hp hne hprime
  obtain ⟨t, htcard, htbij⟩ :=
    exists_nineteen_cubicSurfaceCoordinatePoint_evaluation_bijective
      p hp hne hprime
  have htdir : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
    intro u hu v hv huv a
    exact finset_cubicSurfaceCoordinatePointEvaluation_bijective_no_smul
      p hp t htbij hu hv huv a
  have hstlt : s.card < t.card := by omega
  obtain ⟨x, hxt, hxdir⟩ :=
    exists_cubicSurfaceAffinePoint_direction_outside_of_card_lt p s t hstlt htdir
  have hxnot : x ∉ s := by
    intro hxs
    exact (hxdir x hxs 1) (by simp)
  refine ⟨insert x s, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxnot, hscard]
  · intro L _ f q hq hvan
    exact quadraticAvoidance_fieldExtension_of_bijective f p s hscard hsbij q hq
      (fun y hy ↦ hvan y (Finset.mem_insert_of_mem hy))
  · intro u hu v hv huv a
    rcases Finset.mem_insert.mp hu with hux | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact (huv rfl).elim
      · exact not_smul_symm_of_nonzero x.1 v.1 v.2.2 (hxdir v hv) a
    · rcases Finset.mem_insert.mp hv with hvx | hv
      · subst v
        exact hxdir u hu a
      · exact hsdir u hu v hv huv a

/-- The degree-ten point configuration is realized by an actual ordered
configuration-scheme point of the cubic surface.  Its cone representatives
still witness the strict quadratic-section inequality, while the prescribed
configuration coordinates are the corresponding normalized projective
points. -/
theorem exists_eleven_cubicSurfaceQuadraticAvoidance_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ r : MvPolynomial (Fin 4) K, r.IsHomogeneous 2 →
        (∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨s, hscard, hquad, hsdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hquad, hsdir,
    hq, haBase, haCoordinates⟩

/-- The quadratic Cayley--Bacharach configuration is realized by an actual
ordered field point of the configuration scheme.  This supplies the distinct
projective points that the local Serre calculation uses, while retaining the
condition after each one-point deletion. -/
theorem exists_eleven_cubicSurfaceQuadraticCayleyBacharach_orderedConfigurationFieldPoint
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ y ∈ s, ∀ r : MvPolynomial (Fin 4) K, r.IsHomogeneous 2 →
        (∀ z ∈ s, z ≠ y → MvPolynomial.aeval z.1 r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨s, hscard, hCB, hsdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hCB, hsdir,
    hq, haBase, haCoordinates⟩

/-- The ordered quadratic Cayley--Bacharach configuration retains its
one-point-deletion property after every coefficient-field extension. -/
theorem exists_eleven_cubicSurfaceQuadraticCayleyBacharach_orderedConfigurationFieldPoint_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) (y : cubicSurfaceAffinePoints p), y ∈ s →
        ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous 2 →
          (∀ z ∈ s, z ≠ y → MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨s, hscard, hCB, hsdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_quadratic_cayley_bacharach_fieldExtension
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hCB, hsdir,
    hq, haBase, haCoordinates⟩

/-- The ordered C--B configuration detects every homogeneous form of degree
at most two after deleting any marked point, over every coefficient-field
extension.  It keeps the same actual configuration-scheme point and its
normalized coordinates. -/
theorem exists_eleven_cubicSurfaceLowDegreeCayleyBacharach_orderedConfigurationFieldPoint_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) (y : cubicSurfaceAffinePoints p), y ∈ s →
        ∀ {d : ℕ}, d ≤ 2 → ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous d →
          (∀ z ∈ s, z ≠ y → MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨s, hscard, hCB, hsdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_lowDegree_cayley_bacharach_fieldExtension
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hCB, hsdir,
    hq, haBase, haCoordinates⟩

/-- The ordered eleven-point configuration can be chosen so that its cone
coordinates retain quadratic avoidance after every common field extension. -/
theorem exists_eleven_cubicSurfaceQuadraticAvoidance_orderedConfigurationFieldPoint_fieldExtension
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L)
        (r : MvPolynomial (Fin 4) L), r.IsHomogeneous 2 →
          (∀ x ∈ s, MvPolynomial.aeval (fun i ↦ f (x.1 i)) r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      ∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i := by
  obtain ⟨s, hscard, hquad, hsdir⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_quadrics_independent_directions_fieldExtension
      p hp hne hprime
  obtain ⟨c, hcommon, e, q, a, hq, haBase, haCoordinates⟩ :=
    exists_orderedConfigurationFieldPoint_of_cubicSurfaceAffineDirectionData
      p hp s hscard hsdir
  exact ⟨s, c, hcommon, e, q, a, hscard, hquad, hsdir,
    hq, haBase, haCoordinates⟩

/-- The concrete eleven-point configuration kills every homogeneous form of
degree at most two.  This packages the low-degree section-avoidance witness
needed before passing from a concrete cubic-surface configuration to the
generic configuration argument. -/
theorem exists_eleven_cubicSurfaceAffinePoints_no_nonzero_homogeneous_of_degree_le_two
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      s.card = 11 ∧
      (∀ x ∈ s, MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) ∧
      ∀ {e : ℕ}, e ≤ 2 → ∀ r : MvPolynomial (Fin 4) K,
        r.IsHomogeneous e →
        (∀ x ∈ s, MvPolynomial.aeval x.1 r = 0) → r = 0 := by
  obtain ⟨s, c, hcommon, e, q, a, hscard, hquad, hsdir,
    hq, haBase, haCoordinates⟩ :=
    exists_eleven_cubicSurfaceQuadraticAvoidance_orderedConfigurationFieldPoint
      p hp hne hprime
  have hs : s.Nonempty := by
    apply Finset.card_pos.mp
    omega
  refine ⟨s, c, hscard, hcommon, ?_⟩
  intro d hd r hr hrvan
  exact quadraticAvoidance_homogeneous_of_le_two p s c hs hcommon hquad hd r hr hrvan

/-- Equivalently, the same eleven points make finite evaluation injective on
each full homogeneous system of degree at most two. -/
theorem exists_eleven_cubicSurfaceAffinePoints_low_degree_evaluation_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      s.card = 11 ∧
      (∀ x ∈ s, MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) ∧
      ∀ {e : ℕ}, e ≤ 2 →
        Function.Injective ((finsetEvaluation s).comp
          (cubicSurfacePointEvaluation p
            (MvPolynomial.homogeneousSubmodule (Fin 4) K e))) := by
  obtain ⟨s, c, hscard, hcommon, hlow⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_homogeneous_of_degree_le_two
      p hp hne hprime
  refine ⟨s, c, hscard, hcommon, ?_⟩
  intro e he
  apply finset_cubicSurfacePointEvaluation_injective_of_no_vanishing p s
  intro r hr hrvan
  exact hlow he r hr hrvan

/-- The same eleven points separate the degree-zero, one, and two pieces of
the cubic surface's homogeneous coordinate ring. -/
theorem exists_eleven_cubicSurfaceAffinePoints_low_degree_coordinate_evaluation_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      s.card = 11 ∧
      (∀ x ∈ s, MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0) ∧
      ∀ {e : ℕ}, e ≤ 2 →
        Function.Injective ((finsetEvaluation s).comp
          (cubicSurfaceCoordinatePointEvaluation p hp (d := e))) := by
  obtain ⟨s, c, hscard, hcommon, hlow⟩ :=
    exists_eleven_cubicSurfaceAffinePoints_no_nonzero_homogeneous_of_degree_le_two
      p hp hne hprime
  refine ⟨s, c, hscard, hcommon, ?_⟩
  intro e he
  apply finset_cubicSurfaceCoordinatePointEvaluation_injective_of_no_vanishing p hp s
  intro r hr hrvan
  exact hlow he r hr hrvan

/-- The concrete C--B configuration also supplies the actual rank-eleven
finite subscheme of its cubic-surface fiber.  Its ideal-defined finite étale
family retains delete-one detection for every homogeneous degree at most two,
over every coefficient-field extension. -/
theorem exists_eleven_cubicSurfaceQuadraticAvoidance_finiteSubscheme
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    ∃ s : Finset (cubicSurfaceAffinePoints p), ∃ c : Fin 4 → K,
      ∃ hcommon : ∀ x ∈ s,
        MvPolynomial.aeval x.1 (homogeneousLinearForm c) ≠ 0,
      ∃ e : Fin 11 ≃ s,
      ∃ q : Fin 11 → (AlgebraicGeometry.Spec (.of K) ⟶
        AllCharacteristics.HomogeneousProjective.hypersurface p hp),
      ∃ a : AlgebraicGeometry.Spec (.of K) ⟶
        (AllCharacteristics.orderedFamilyConfigurationOver
          (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).left,
      s.card = 11 ∧
      (∀ {L : Type u} [Field L] (f : K →+* L) (y : cubicSurfaceAffinePoints p), y ∈ s →
        ∀ {d : ℕ}, d ≤ 2 → ∀ r : MvPolynomial (Fin 4) L, r.IsHomogeneous d →
          (∀ z ∈ s, z ≠ y → MvPolynomial.aeval (fun i => f (z.1 i)) r = 0) → r = 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ scalar : K, y.1 ≠ scalar • x.1) ∧
      (∀ i, q i = cubicSurfaceAffinePointLinearNormalizedProjectivePoint p hp c (e i).1
        (hcommon (e i).1 (e i).2)) ∧
      a ≫ (AllCharacteristics.orderedFamilyConfigurationOver
        (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      (∀ i, (a ≫ Over.Hom.left
          (AllCharacteristics.orderedFamilyConfigurationι
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11)) ≫
          (AllCharacteristics.orderedFamilyCoordinate
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11 i).left = q i) ∧
      ∃ D : AllCharacteristics.FiniteSubschemeDatum
        (pullback.snd
          (pullback.snd
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
            (AllCharacteristics.orderedFamilyConfigurationOver
              (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a) 11,
        let f := pullback.snd
          (pullback.snd
            (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
            (AllCharacteristics.orderedFamilyConfigurationOver
              (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) 11).hom) a
        letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
        AllCharacteristics.finiteSchemeRank (D.val.subschemeι ≫ f) = 11 ∧
          Etale (D.val.subschemeι ≫ f) := by
  obtain ⟨s, c, hcommon, e, q, a, hscard, hCB, hsdir,
    hq, haBase, haCoordinates⟩ :=
    exists_eleven_cubicSurfaceLowDegreeCayleyBacharach_orderedConfigurationFieldPoint_fieldExtension
      p hp hne hprime
  refine ⟨s, c, hcommon, e, q, a, hscard, hCB, hsdir, hq, haBase,
    haCoordinates, cubicSurfaceOrderedConfigurationFiberFiniteSubscheme p hp a, ?_⟩
  exact ⟨cubicSurfaceOrderedConfigurationFiberFiniteSubscheme_rank p hp a,
    cubicSurfaceOrderedConfigurationFiberFiniteSubscheme_toBase_etale p hp a⟩

end PfaffianDescent
