import PfaffianDescent.TripleCompleteIntersectionHilbert
import PfaffianDescent.TwoQuadricsNoIrrelevantSocle

/-!
# Graded detection of regularity in a quadratic pencil

For a homogeneous cubic--quadric pair, multiplication by a second quadric
preserves the homogeneous pieces of the quotient.  This file records that
the second quadric is regular modulo the pair exactly when all of these
finite-dimensional multiplication maps are injective.  It is the algebraic
bridge from Voisin's no-fixed-component condition to determinantal rank
conditions.
-/

namespace PfaffianDescent

open MvPolynomial

section

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-`d` piece of the quotient by a cubic--quadric pair. -/
noncomputable def cubicQuadricComponent
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Submodule K
      (MvPolynomial (Fin 4) K ⧸
        Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :=
  (FourHomogeneous K d).map
    (Ideal.Quotient.mkₐ K
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))).toLinearMap

noncomputable instance cubicQuadricComponent_finite
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Module.Finite K (cubicQuadricComponent p q d) := by
  unfold cubicQuadricComponent
  infer_instance

/-- Multiplication by a homogeneous quadric on one graded piece of the
cubic--quadric quotient. -/
noncomputable def cubicQuadricGradedMultiplication
    (p q r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2) (d : ℕ) :
    cubicQuadricComponent p q d →ₗ[K] cubicQuadricComponent p q (d + 2) where
  toFun y := by
    let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
    refine ⟨Ideal.Quotient.mk I r * y.1, ?_⟩
    obtain ⟨f, hfd, hf⟩ := y.2
    refine ⟨r * f, ?_, ?_⟩
    · change (r * f).IsHomogeneous (d + 2)
      simpa only [Nat.add_comm] using hr.mul hfd
    · change Ideal.Quotient.mk I (r * f) = _
      rw [map_mul]
      congr 1
  map_add' y z := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add]
  map_smul' a y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, RingHom.id_apply, mul_smul_comm]

/-- Regularity modulo the cubic--quadric pair makes multiplication injective
on every homogeneous quotient piece. -/
theorem cubicQuadricGradedMultiplication_injective_of_regular
    (p q r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2)
    (hregular : ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (d : ℕ) :
    Function.Injective (cubicQuadricGradedMultiplication p q r hr d) := by
  intro y z hyz
  apply sub_eq_zero.mp
  apply Subtype.ext
  obtain ⟨f, hfd, hf⟩ := (y - z).2
  rw [← hf]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmul : cubicQuadricGradedMultiplication p q r hr d (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  have hprod : r * f ∈
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hval := congrArg Subtype.val hmul
    change Ideal.Quotient.mk
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r *
        (y - z).1 = 0 at hval
    rw [← hf] at hval
    change Ideal.Quotient.mk
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r *
        Ideal.Quotient.mk
          (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) f = 0 at hval
    rw [← map_mul] at hval
    exact hval
  exact hregular f hprod

/-- If multiplication by the second quadric is injective on every graded
piece, then it is regular modulo the cubic--quadric pair on the whole
polynomial ring. -/
theorem regular_of_cubicQuadricGradedMultiplication_injective
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hinj : ∀ d : ℕ,
      Function.Injective (cubicQuadricGradedMultiplication p q r hr d)) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
    apply Ideal.homogeneous_span
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨3, hp⟩
    · exact ⟨2, hq⟩
  intro f hrf
  change f ∈ I
  rw [← sum_homogeneousComponent f]
  apply I.sum_mem
  intro d hd
  let fd : FourHomogeneous K d :=
    ⟨homogeneousComponent d f, homogeneousComponent_isHomogeneous d f⟩
  let y : cubicQuadricComponent p q d :=
    ⟨Ideal.Quotient.mk I fd.1, ⟨fd.1, fd.2, rfl⟩⟩
  have hcomponent : r * fd.1 ∈ I := by
    have hmem := homogeneousComponent_mem_of_mem hI hrf (2 + d)
    rw [homogeneousComponent_mul_left hr d] at hmem
    exact hmem
  have hymul : cubicQuadricGradedMultiplication p q r hr d y = 0 := by
    apply Subtype.ext
    change Ideal.Quotient.mk I r * Ideal.Quotient.mk I fd.1 = 0
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomponent
  have hyzero : y = 0 := by
    apply hinj d
    simpa using hymul
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact congrArg Subtype.val hyzero

/-- Regularity of a quadratic pencil member is equivalent to injectivity of
all its finite-dimensional graded multiplication maps. -/
theorem cubicQuadricGradedMultiplication_injective_iff_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) :
    (∀ d : ℕ,
      Function.Injective (cubicQuadricGradedMultiplication p q r hr d)) ↔
      ∀ f : MvPolynomial (Fin 4) K,
        r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  constructor
  · exact regular_of_cubicQuadricGradedMultiplication_injective p q r hp hq hr
  · intro hregular d
    exact cubicQuadricGradedMultiplication_injective_of_regular
      p q r hr hregular d

/-- Failure of regularity is detected in at least one finite homogeneous
degree. -/
theorem exists_degree_cubicQuadricGradedMultiplication_not_injective_of_not_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hnot : ¬ ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ d : ℕ,
      ¬ Function.Injective (cubicQuadricGradedMultiplication p q r hr d) := by
  simpa only [not_forall] using
    (not_congr
      (cubicQuadricGradedMultiplication_injective_iff_regular
        p q r hp hq hr)).mpr hnot

/-- The graded multiplication maps have finite-dimensional source and
target, so their injectivity is a literal finite rank condition. -/
theorem cubicQuadricGradedMultiplication_injective_iff_finrank_ker_eq_zero
    (p q r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2) (d : ℕ) :
    Function.Injective (cubicQuadricGradedMultiplication p q r hr d) ↔
      Module.finrank K (LinearMap.ker
        (cubicQuadricGradedMultiplication p q r hr d)) = 0 := by
  rw [← LinearMap.ker_eq_bot, Submodule.finrank_eq_zero]

/-- Nonregularity produces a positive-dimensional kernel in one finite
graded multiplication matrix. -/
theorem exists_degree_cubicQuadricGradedMultiplication_finrank_ker_pos_of_not_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (hnot : ¬ ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ d : ℕ, 0 < Module.finrank K (LinearMap.ker
      (cubicQuadricGradedMultiplication p q r hr d)) := by
  obtain ⟨d, hd⟩ :=
    exists_degree_cubicQuadricGradedMultiplication_not_injective_of_not_regular
      p q r hp hq hr hnot
  refine ⟨d, Nat.pos_of_ne_zero ?_⟩
  intro hzero
  exact hd ((cubicQuadricGradedMultiplication_injective_iff_finrank_ker_eq_zero
    p q r hr d).mpr hzero)

/-- A nonzero kernel class for multiplication by the second quadric can be
propagated by at least one homogeneous coordinate.  The regular pair has no
class annihilated by all four coordinates, so the propagated class remains
nonzero. -/
theorem exists_next_degree_cubicQuadricGradedMultiplication_kernel
    (p q r : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0)
    (hrel : IsRelPrime p q) (hr : r.IsHomogeneous 2) (d : ℕ)
    (y : cubicQuadricComponent p q d)
    (hy0 : y ≠ 0)
    (hyker : cubicQuadricGradedMultiplication p q r hr d y = 0) :
    ∃ z : cubicQuadricComponent p q (d + 1), z ≠ 0 ∧
      cubicQuadricGradedMultiplication p q r hr (d + 1) z = 0 := by
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  have hnotall : ¬ ∀ j : Fin 4,
      Ideal.Quotient.mk I (X j) * y.1 = 0 := by
    intro hall
    have hyval : y.1 = 0 :=
      two_quadrics_no_irrelevant_annihilator p q hp0 hrel y.1 hall
    apply hy0
    apply Subtype.ext
    exact hyval
  push Not at hnotall
  obtain ⟨j, hj⟩ := hnotall
  obtain ⟨f, hfd, hf⟩ := y.2
  let z : cubicQuadricComponent p q (d + 1) :=
    ⟨Ideal.Quotient.mk I (X j) * y.1, ⟨X j * f, by
      change (X j * f).IsHomogeneous (d + 1)
      simpa only [Nat.add_comm] using (isHomogeneous_X (R := K) j).mul hfd, by
      change Ideal.Quotient.mk I f = y.1 at hf
      change Ideal.Quotient.mk I (X j * f) = _
      rw [map_mul, hf]⟩⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    apply hj
    exact congrArg Subtype.val hz
  · apply Subtype.ext
    have hval := congrArg Subtype.val hyker
    change Ideal.Quotient.mk I r * y.1 = 0 at hval
    change Ideal.Quotient.mk I r *
      (Ideal.Quotient.mk I (X j) * y.1) = 0
    calc
      Ideal.Quotient.mk I r * (Ideal.Quotient.mk I (X j) * y.1) =
          Ideal.Quotient.mk I (X j) * (Ideal.Quotient.mk I r * y.1) := by ring
      _ = 0 := by rw [hval, mul_zero]

/-- A nonzero kernel class propagates through every higher homogeneous
degree. -/
theorem exists_higher_degree_cubicQuadricGradedMultiplication_kernel
    (p q r : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0)
    (hrel : IsRelPrime p q) (hr : r.IsHomogeneous 2) (d : ℕ)
    (y : cubicQuadricComponent p q d)
    (hy0 : y ≠ 0)
    (hyker : cubicQuadricGradedMultiplication p q r hr d y = 0) :
    ∀ n : ℕ, ∃ z : cubicQuadricComponent p q (d + n), z ≠ 0 ∧
      cubicQuadricGradedMultiplication p q r hr (d + n) z = 0 := by
  intro n
  induction n with
  | zero =>
      simpa only [Nat.add_zero] using ⟨y, hy0, hyker⟩
  | succ n ih =>
      obtain ⟨z, hz0, hzker⟩ := ih
      obtain ⟨w, hw0, hwker⟩ :=
        exists_next_degree_cubicQuadricGradedMultiplication_kernel
          p q r hp0 hrel hr (d + n) z hz0 hzker
      simpa only [Nat.add_assoc, Nat.add_right_comm, Nat.add_comm] using
        ⟨w, hw0, hwker⟩

/-- If the second quadric is not regular modulo the cubic--quadric pair,
then positive kernel dimension occurs in arbitrarily high degrees. -/
theorem arbitrarily_high_degree_kernel_of_not_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    (hnot : ¬ ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      0 < Module.finrank K (LinearMap.ker
        (cubicQuadricGradedMultiplication p q r hr d)) := by
  obtain ⟨d₀, hd₀⟩ :=
    exists_degree_cubicQuadricGradedMultiplication_not_injective_of_not_regular
      p q r hp hq hr hnot
  rw [← LinearMap.ker_eq_bot] at hd₀
  obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hd₀)
  have hy0' : y ≠ 0 := by simpa using hy0
  have hyker : cubicQuadricGradedMultiplication p q r hr d₀ y = 0 := hy
  intro N
  obtain ⟨z, hz0, hzker⟩ :=
    exists_higher_degree_cubicQuadricGradedMultiplication_kernel
      p q r hp0 hrel hr d₀ y hy0' hyker N
  refine ⟨d₀ + N, Nat.le_add_left N d₀, Nat.pos_of_ne_zero ?_⟩
  intro hzero
  have hbot : LinearMap.ker
      (cubicQuadricGradedMultiplication p q r hr (d₀ + N)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hzmem : z ∈ LinearMap.ker
      (cubicQuadricGradedMultiplication p q r hr (d₀ + N)) := hzker
  rw [hbot] at hzmem
  exact hz0 (by simpa using hzmem)

end

end PfaffianDescent
