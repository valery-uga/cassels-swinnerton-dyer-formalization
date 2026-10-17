import PfaffianDescent.TwoGeneratorKoszul
import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.HomogeneousDimensions
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual degreewise resolution of Coray's cubic--degree-n curve

SOURCE DRAFT / UNVERIFIED.

The Koszul maps and quotient below use the actual polynomial equations.
This is the Hilbert-function prerequisite to Coray's complete-intersection
arithmetic-genus calculation. It does not assert a normalization, genus
bound, or Riemann--Roch theorem. The second equation has arbitrary degree n;
the earlier cubic--quadric calculation in the project handles only n=2.
-/

namespace PfaffianDescent.Coray
open MvPolynomial Module
universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev CurveHomogeneous (K : Type u) [Field K] (d : ℕ) :=
  homogeneousSubmodule (Fin 4) K d

/-- The actual degree-d subspace of the quotient by the two curve equations. -/
noncomputable def curveComponent (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K ⧸
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :=
  (CurveHomogeneous K d).map
    (Ideal.Quotient.mkₐ K
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))).toLinearMap

noncomputable instance curveComponent_finite
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Module.Finite K (curveComponent p q d) := by
  unfold curveComponent
  infer_instance

noncomputable def curveGradedFirst {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (d : ℕ) :
    CurveHomogeneous K d →ₗ[K]
      CurveHomogeneous K (d + n) × CurveHomogeneous K (d + 3) where
  toFun x :=
    (⟨-q * x.val, by
       change (-q * x.val).IsHomogeneous (d + n)
       simpa only [Nat.add_comm] using hq.neg.mul x.property⟩,
     ⟨p * x.val, by
       change (p * x.val).IsHomogeneous (d + 3)
       simpa only [Nat.add_comm] using hp.mul x.property⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_smul_comm]

noncomputable def curveGradedLast {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (d : ℕ) :
    (CurveHomogeneous K (d + n) × CurveHomogeneous K (d + 3)) →ₗ[K]
      CurveHomogeneous K (d + n + 3) where
  toFun x := ⟨p * x.1.val + q * x.2.val, by
    apply IsHomogeneous.add
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hp.mul x.1.property
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hq.mul x.2.property⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    ring
  map_smul' a x := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      RingHom.id_apply, mul_smul_comm, smul_add]

theorem curveGradedFirst_injective {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (d : ℕ) :
    Function.Injective (curveGradedFirst p q hp hq d) := by
  intro x y hxy
  apply Subtype.ext
  exact mul_left_cancel₀ hp0
    (congrArg Subtype.val (congrArg Prod.snd hxy))

/-- Exactness is proved by the existing ungraded Koszul theorem and
homogeneous projection of its actual polynomial preimage. -/
theorem curveGraded_exact_middle {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    LinearMap.range (curveGradedFirst p q hp hq d) =
      LinearMap.ker (curveGradedLast p q hp hq d) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change p * (-q * x.val) + q * (p * x.val) = 0
    ring
  · intro x hx
    have hx' : (x.1.val, x.2.val) ∈ LinearMap.ker (twoGeneratorLast p q) :=
      congrArg Subtype.val hx
    rw [← twoGenerator_exact hp0 hrel] at hx'
    obtain ⟨s, hs⟩ := hx'
    have hps : p * s = x.2.val := congrArg Prod.snd hs
    have hshom : s.IsHomogeneous d := homogeneous_of_mul_right hp hp0 (by
      rw [mul_comm s p, hps]
      exact x.2.property)
    exact ⟨⟨s, hshom⟩,
      Prod.ext (Subtype.ext (congrArg Prod.fst hs)) (Subtype.ext hps)⟩

noncomputable def curveProjection (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    CurveHomogeneous K d →ₗ[K] curveComponent p q d where
  toFun x :=
    ⟨Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) x.val,
      ⟨x.val, x.property, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (Ideal.Quotient.mkₐ K
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))) a x.val

theorem curveProjection_surjective
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Function.Surjective (curveProjection p q d) := by
  rintro ⟨y, f, hfd, hf⟩
  exact ⟨⟨f, hfd⟩, Subtype.ext hf⟩

/-- The projected quotient relations are exactly the image of the actual
last Koszul map, without assuming ideal saturation or curve reducedness. -/
theorem curveProjection_exact {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (d : ℕ) :
    LinearMap.range (curveGradedLast p q hp hq d) =
      LinearMap.ker (curveProjection p q (d + n + 3)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hzero : Ideal.Quotient.mk
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
        (p * x.1.val + q * x.2.val) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.add_mem
      · apply Ideal.mul_mem_right
        exact Ideal.subset_span (Set.mem_insert p {q})
      · apply Ideal.mul_mem_right
        exact Ideal.subset_span (Set.mem_insert_of_mem p (Set.mem_singleton q))
    exact Subtype.ext hzero
  · intro x hx
    have hxval := congrArg Subtype.val hx
    change Ideal.Quotient.mk
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) x.val = 0 at hxval
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hxval
    rw [← twoGeneratorLast_range] at hmem
    obtain ⟨⟨a, b⟩, hab⟩ := hmem
    let a' := homogeneousComponent (d + n) a
    let b' := homogeneousComponent (d + 3) b
    refine ⟨(⟨a', homogeneousComponent_isHomogeneous _ _⟩,
      ⟨b', homogeneousComponent_isHomogeneous _ _⟩), ?_⟩
    apply Subtype.ext
    change p * a' + q * b' = x.val
    have hpa : homogeneousComponent (d + n + 3) (p * a) = p * a' := by
      rw [show d + n + 3 = 3 + (d + n) by omega]
      exact homogeneousComponent_mul_left hp (d + n)
    have hqb : homogeneousComponent (d + n + 3) (q * b) = q * b' := by
      rw [show d + n + 3 = n + (d + 3) by omega]
      exact homogeneousComponent_mul_left hq (d + 3)
    change p * a + q * b = x.val at hab
    rw [← hpa, ← hqb, ← map_add, hab,
      homogeneousComponent_eq_self x.property]

/-- Hilbert-function identity for the actual cubic--degree-n intersection.
This establishes the graded-resolution input to the arithmetic-genus
formula, rather than assuming that formula as a curve certificate. -/
theorem curve_hilbert_identity {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    finrank K (curveComponent p q (d + n + 3)) +
      (finrank K (CurveHomogeneous K (d + n)) +
        finrank K (CurveHomogeneous K (d + 3))) =
      finrank K (CurveHomogeneous K (d + n + 3)) +
        finrank K (CurveHomogeneous K d) := by
  let F := curveGradedFirst p q hp hq d
  let L := curveGradedLast p q hp hq d
  let Q := curveProjection p q (d + n + 3)
  have hF := F.finrank_range_add_finrank_ker
  have hL := L.finrank_range_add_finrank_ker
  have hQ := Q.finrank_range_add_finrank_ker
  have hFinj : Function.Injective F := curveGradedFirst_injective p q hp hq hp0 d
  have hFL : LinearMap.range F = LinearMap.ker L :=
    curveGraded_exact_middle p q hp hq hp0 hrel d
  have hLQ : LinearMap.range L = LinearMap.ker Q := curveProjection_exact p q hp hq d
  have hQsurj : Function.Surjective Q := curveProjection_surjective p q (d + n + 3)
  dsimp only [F, L, Q] at hF hL hQ hFinj hFL hLQ hQsurj
  rw [LinearMap.ker_eq_bot.mpr hFinj, finrank_bot, add_zero] at hF
  rw [← hFL, hF, Module.finrank_prod] at hL
  rw [LinearMap.range_eq_top.mpr hQsurj, finrank_top, ← hLQ] at hQ
  omega

/-- The same identity expressed by the already proved monomial counts. -/
theorem curve_hilbert_choose_identity {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    finrank K (curveComponent p q (d + n + 3)) +
      ((d + n + 3).choose 3 + (d + 6).choose 3) =
      (d + n + 6).choose 3 + (d + 3).choose 3 := by
  have h := curve_hilbert_identity p q hp hq hp0 hrel d
  simpa only [CurveHomogeneous, four_variable_homogeneous_finrank,
    Nat.add_assoc] using h

end PfaffianDescent.Coray
