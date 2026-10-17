import PfaffianDescent.VoisinQuadraticPencilGradedRegularity

/-!
# Hilbert detection for a quadratic pencil

The degreewise quotient map from a cubic--quadric complete intersection to
the quotient by a second quadric is surjective.  Its kernel is the image of
multiplication by that second quadric.  This is the finite-dimensional exact
sequence which turns persistent multiplication kernels into an eventual
Hilbert-function obstruction.
-/

namespace PfaffianDescent

open MvPolynomial

section

variable {K : Type*} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable instance tripleCompleteIntersectionComponent_finite
    (p q r : MvPolynomial (Fin 4) K) (d : ℕ) :
    Module.Finite K (tripleCompleteIntersectionComponent p q r d) := by
  unfold tripleCompleteIntersectionComponent
  infer_instance

private lemma cubicQuadricIdeal_le_tripleIdeal
    (p q r : MvPolynomial (Fin 4) K) :
    Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤
      tripleCompleteIntersectionIdeal p q r := by
  apply Ideal.span_mono
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
  rcases hf with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

/-- The first homogeneous Koszul map for a cubic and a quadric, in total
degree `d + 5`. -/
noncomputable def cubicQuadricGradedFirst
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    FourHomogeneous K d →ₗ[K]
      FourHomogeneous K (d + 2) × FourHomogeneous K (d + 3) where
  toFun x :=
    (⟨-q * x.val, by
      change (-q * x.val).IsHomogeneous (d + 2)
      simpa only [Nat.add_comm] using hq.neg.mul x.property⟩,
    ⟨p * x.val, by
      change (p * x.val).IsHomogeneous (d + 3)
      simpa only [Nat.add_comm] using hp.mul x.property⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

/-- The last homogeneous Koszul map for a cubic and a quadric, in total
degree `d + 5`. -/
noncomputable def cubicQuadricGradedLast
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    (FourHomogeneous K (d + 2) × FourHomogeneous K (d + 3)) →ₗ[K]
      FourHomogeneous K (d + 5) where
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

theorem cubicQuadricGradedFirst_injective
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (d : ℕ) :
    Function.Injective (cubicQuadricGradedFirst p q hp hq d) := by
  intro x y hxy
  apply Subtype.ext
  exact twoGeneratorFirst_injective hp0
    (Prod.ext (congrArg Subtype.val (congrArg Prod.fst hxy))
      (congrArg Subtype.val (congrArg Prod.snd hxy)))

theorem cubicQuadricGraded_exact_middle
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedFirst p q hp hq d) =
      LinearMap.ker (cubicQuadricGradedLast p q hp hq d) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun (twoGenerator_comp_zero p q) x.val
  · intro x hx
    have hx' : (x.1.val, x.2.val) ∈
        LinearMap.ker (twoGeneratorLast p q) := by
      have hxval := congrArg Subtype.val hx
      change p * x.1.val + q * x.2.val = 0 at hxval
      exact hxval
    rw [← twoGenerator_exact hp0 hrel] at hx'
    obtain ⟨s, hs⟩ := hx'
    have hps : p * s = x.2.val := congrArg Prod.snd hs
    have hshom : s.IsHomogeneous d := homogeneous_of_mul_right hp hp0 (by
      rw [mul_comm s p, hps]
      exact x.2.property)
    exact ⟨⟨s, hshom⟩,
      Prod.ext (Subtype.ext (congrArg Prod.fst hs)) (Subtype.ext hps)⟩

/-- Projection from degree `d` polynomials to the corresponding homogeneous
piece of the cubic--quadric quotient. -/
noncomputable def cubicQuadricProjection
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    FourHomogeneous K d →ₗ[K] cubicQuadricComponent p q d where
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

theorem cubicQuadricProjection_surjective
    (p q : MvPolynomial (Fin 4) K) (d : ℕ) :
    Function.Surjective (cubicQuadricProjection p q d) := by
  rintro ⟨y, f, hfd, hf⟩
  exact ⟨⟨f, hfd⟩, Subtype.ext hf⟩

theorem cubicQuadricProjection_exact
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedLast p q hp hq d) =
      LinearMap.ker (cubicQuadricProjection p q (d + 5)) := by
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
    let a' := homogeneousComponent (d + 2) a
    let b' := homogeneousComponent (d + 3) b
    refine ⟨(⟨a', homogeneousComponent_isHomogeneous _ _⟩,
      ⟨b', homogeneousComponent_isHomogeneous _ _⟩), ?_⟩
    apply Subtype.ext
    change p * a' + q * b' = x.val
    have hpa : homogeneousComponent (d + 5) (p * a) = p * a' := by
      rw [show d + 5 = 3 + (d + 2) by omega]
      exact homogeneousComponent_mul_left hp (d + 2)
    have hqb : homogeneousComponent (d + 5) (q * b) = q * b' := by
      rw [show d + 5 = 2 + (d + 3) by omega]
      exact homogeneousComponent_mul_left hq (d + 3)
    change p * a + q * b = x.val at hab
    rw [← hpa, ← hqb, ← map_add, hab,
      homogeneousComponent_eq_self x.property]

/-- Euler-characteristic identity for the homogeneous Koszul resolution of
a relatively prime cubic--quadric pair. -/
theorem cubicQuadric_hilbert_identity
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    Module.finrank K (cubicQuadricComponent p q (d + 5)) +
        (Module.finrank K (FourHomogeneous K (d + 2)) +
          Module.finrank K (FourHomogeneous K (d + 3))) =
      Module.finrank K (FourHomogeneous K (d + 5)) +
        Module.finrank K (FourHomogeneous K d) := by
  let F := cubicQuadricGradedFirst p q hp hq d
  let L := cubicQuadricGradedLast p q hp hq d
  let Q := cubicQuadricProjection p q (d + 5)
  have hF := F.finrank_range_add_finrank_ker
  have hL := L.finrank_range_add_finrank_ker
  have hQ := Q.finrank_range_add_finrank_ker
  have hFinj : Function.Injective F :=
    cubicQuadricGradedFirst_injective p q hp hq hp0 d
  have hFL : LinearMap.range F = LinearMap.ker L :=
    cubicQuadricGraded_exact_middle p q hp hq hp0 hrel d
  have hLQ : LinearMap.range L = LinearMap.ker Q :=
    cubicQuadricProjection_exact p q hp hq d
  have hQsurj : Function.Surjective Q := cubicQuadricProjection_surjective p q (d + 5)
  dsimp only [F, L, Q] at hF hL hQ hFinj hFL hLQ hQsurj
  rw [LinearMap.ker_eq_bot.mpr hFinj, finrank_bot, add_zero] at hF
  rw [← hFL, hF, Module.finrank_prod] at hL
  rw [LinearMap.range_eq_top.mpr hQsurj, finrank_top, ← hLQ] at hQ
  omega

/-- In high degrees the Hilbert function of a cubic--quadric complete
intersection increases by twelve when the degree increases by two. -/
theorem cubicQuadricComponent_finrank_add_two
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    Module.finrank K (cubicQuadricComponent p q (d + 7)) =
      Module.finrank K (cubicQuadricComponent p q (d + 5)) + 12 := by
  have h₀ := cubicQuadric_hilbert_identity p q hp hq hp0 hrel d
  have h₂ := cubicQuadric_hilbert_identity p q hp hq hp0 hrel (d + 2)
  have hidx : d + 2 + 5 = d + 7 := by omega
  rw [hidx] at h₂
  simp only [four_homogeneous_finrank] at h₀ h₂
  norm_num [Nat.add_assoc] at h₀ h₂
  have hchoose := cubic_two_quadrics_choose_identity d
  omega

/-- The degreewise quotient map obtained by adding the second quadric to the
cubic--quadric ideal. -/
noncomputable def cubicQuadricToTripleComponent
    (p q r : MvPolynomial (Fin 4) K) (d : ℕ) :
    cubicQuadricComponent p q d →ₗ[K]
      tripleCompleteIntersectionComponent p q r d where
  toFun y := by
    let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
    let J := tripleCompleteIntersectionIdeal p q r
    let φ := Ideal.Quotient.factorₐ K (cubicQuadricIdeal_le_tripleIdeal p q r)
    refine ⟨φ y.1, ?_⟩
    obtain ⟨f, hfd, hf⟩ := y.2
    refine ⟨f, hfd, ?_⟩
    change Ideal.Quotient.mk I f = y.1 at hf
    change Ideal.Quotient.mk J f = φ y.1
    rw [← hf]
    exact (Ideal.Quotient.factor_mk
      (cubicQuadricIdeal_le_tripleIdeal p q r) f).symm
  map_add' y z := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a y := by
    apply Subtype.ext
    exact map_smul (Ideal.Quotient.factorₐ K
      (cubicQuadricIdeal_le_tripleIdeal p q r)) a y.1

/-- Adding the second quadric gives a surjection on every homogeneous
component. -/
theorem cubicQuadricToTripleComponent_surjective
    (p q r : MvPolynomial (Fin 4) K) (d : ℕ) :
    Function.Surjective (cubicQuadricToTripleComponent p q r d) := by
  intro z
  obtain ⟨f, hfd, hf⟩ := z.2
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let y : cubicQuadricComponent p q d :=
    ⟨Ideal.Quotient.mk I f, ⟨f, hfd, rfl⟩⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (tripleCompleteIntersectionIdeal p q r) f = z.1
  exact hf

/-- Multiplication by the second quadric lands in the kernel of the map to
the three-equation quotient. -/
theorem cubicQuadricGradedMultiplication_range_le_ker_toTriple
    (p q r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 2) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedMultiplication p q r hr d) ≤
      LinearMap.ker (cubicQuadricToTripleComponent p q r (d + 2)) := by
  rintro _ ⟨y, rfl⟩
  apply Subtype.ext
  change (Ideal.Quotient.factorₐ K (cubicQuadricIdeal_le_tripleIdeal p q r))
      (Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r *
        y.1) = 0
  obtain ⟨f, hfd, hf⟩ := y.2
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  change Ideal.Quotient.mk I f = y.1 at hf
  rw [← hf, map_mul]
  change Ideal.Quotient.mk (tripleCompleteIntersectionIdeal p q r) r *
      Ideal.Quotient.mk (tripleCompleteIntersectionIdeal p q r) f = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  change r * f ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K))
  apply Ideal.mul_mem_right f
  apply Ideal.subset_span
  simp

/-- The kernel of the degreewise quotient map consists exactly of the
multiples of the second quadric from two degrees below. -/
theorem cubicQuadricGradedMultiplication_range_eq_ker_toTriple
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (d : ℕ) :
    LinearMap.range (cubicQuadricGradedMultiplication p q r hr d) =
      LinearMap.ker (cubicQuadricToTripleComponent p q r (d + 2)) := by
  apply le_antisymm
  · exact cubicQuadricGradedMultiplication_range_le_ker_toTriple p q r hr d
  · intro y hy
    obtain ⟨f, hfd, hf⟩ := y.2
    let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
    have hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
      apply Ideal.homogeneous_span
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨3, hp⟩
      · exact ⟨2, hq⟩
    have hJ : f ∈ tripleCompleteIntersectionIdeal p q r := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hval := congrArg Subtype.val hy
      change (Ideal.Quotient.factorₐ K
        (cubicQuadricIdeal_le_tripleIdeal p q r)) y.1 = 0 at hval
      change Ideal.Quotient.mk I f = y.1 at hf
      rw [← hf] at hval
      exact hval
    change f ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) at hJ
    rw [← threeGeneratorLast_range] at hJ
    obtain ⟨⟨a, b, c⟩, habc⟩ := hJ
    let c' := homogeneousComponent d c
    let z : cubicQuadricComponent p q d :=
      ⟨Ideal.Quotient.mk I c',
        ⟨c', homogeneousComponent_isHomogeneous d c, rfl⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I r * Ideal.Quotient.mk I c' = y.1
    rw [← map_mul, ← hf]
    apply Ideal.Quotient.eq.mpr
    have hpa : homogeneousComponent (d + 2) (p * a) ∈ I := by
      apply homogeneousComponent_mem_of_mem hI
      apply Ideal.mul_mem_right a
      exact Ideal.subset_span (Set.mem_insert p {q})
    have hqb : homogeneousComponent (d + 2) (q * b) ∈ I := by
      apply homogeneousComponent_mem_of_mem hI
      apply Ideal.mul_mem_right b
      exact Ideal.subset_span (Set.mem_insert_of_mem p (Set.mem_singleton q))
    have hdeg := congrArg (homogeneousComponent (d + 2)) habc
    change homogeneousComponent (d + 2) (p * a + q * b + r * c) =
      homogeneousComponent (d + 2) f at hdeg
    rw [map_add, map_add,
      homogeneousComponent_eq_self hfd,
      show d + 2 = 2 + d by omega,
      homogeneousComponent_mul_left hr d] at hdeg
    change r * c' - f ∈ I
    rw [← hdeg]
    dsimp only [c']
    convert I.neg_mem (I.add_mem hpa hqb) using 1
    abel_nf

/-- Rank-nullity for the degreewise exact sequence
`A_d → A_{d+2} → B_{d+2} → 0`, where `A` is the quotient by the
cubic and first quadric and `B` is the quotient by all three equations. -/
theorem cubicQuadric_tripleComponent_finrank_identity
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (d : ℕ) :
    Module.finrank K (tripleCompleteIntersectionComponent p q r (d + 2)) +
        Module.finrank K (cubicQuadricComponent p q d) =
      Module.finrank K (cubicQuadricComponent p q (d + 2)) +
        Module.finrank K (LinearMap.ker
          (cubicQuadricGradedMultiplication p q r hr d)) := by
  let M := cubicQuadricGradedMultiplication p q r hr d
  let Q := cubicQuadricToTripleComponent p q r (d + 2)
  have hM := M.finrank_range_add_finrank_ker
  have hQ := Q.finrank_range_add_finrank_ker
  have hQsurj : Function.Surjective Q :=
    cubicQuadricToTripleComponent_surjective p q r (d + 2)
  have hMQ : LinearMap.range M = LinearMap.ker Q :=
    cubicQuadricGradedMultiplication_range_eq_ker_toTriple p q r hp hq hr d
  dsimp only [M, Q] at hM hQ hQsurj hMQ
  rw [LinearMap.range_eq_top.mpr hQsurj, finrank_top, ← hMQ] at hQ
  omega

/-- The excess of the three-equation Hilbert function over the expected
length twelve is exactly the kernel dimension of multiplication by the
second quadric. -/
theorem cubic_two_quadrics_finrank_eq_twelve_add_kernel
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (hp0 : p ≠ 0)
    (hrel : IsRelPrime p q) (d : ℕ) :
    Module.finrank K (tripleCompleteIntersectionComponent p q r (d + 7)) =
      12 + Module.finrank K (LinearMap.ker
        (cubicQuadricGradedMultiplication p q r hr (d + 5))) := by
  have hseq := cubicQuadric_tripleComponent_finrank_identity
    p q r hp hq hr (d + 5)
  have hpair := cubicQuadricComponent_finrank_add_two
    p q hp hq hp0 hrel d
  have hidx : d + 5 + 2 = d + 7 := by omega
  have hseq' :
      Module.finrank K (tripleCompleteIntersectionComponent p q r (d + 7)) +
          Module.finrank K (cubicQuadricComponent p q (d + 5)) =
        Module.finrank K (cubicQuadricComponent p q (d + 7)) +
          Module.finrank K (LinearMap.ker
            (cubicQuadricGradedMultiplication p q r hr (d + 5))) := by
    simpa only [hidx] using hseq
  omega

/-- In every degree at least seven, the expected Hilbert bound twelve is
equivalent to injectivity of multiplication by the second quadric two
degrees below. -/
theorem cubic_two_quadrics_finrank_le_twelve_iff_injective
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (hp0 : p ≠ 0)
    (hrel : IsRelPrime p q) (d : ℕ) :
    Module.finrank K (tripleCompleteIntersectionComponent p q r (d + 7)) ≤ 12 ↔
      Function.Injective
        (cubicQuadricGradedMultiplication p q r hr (d + 5)) := by
  rw [cubic_two_quadrics_finrank_eq_twelve_add_kernel
    p q r hp hq hr hp0 hrel d,
    cubicQuadricGradedMultiplication_injective_iff_finrank_ker_eq_zero]
  omega

/-- An eventual Hilbert-function bound by the expected complete-intersection
length forces the second quadric to be regular.  If regularity failed, kernel
propagation and the exact Hilbert formula would violate the bound in an
arbitrarily high degree. -/
theorem regular_of_eventually_cubic_two_quadrics_finrank_le_twelve
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (hp0 : p ≠ 0)
    (hrel : IsRelPrime p q)
    (hbound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Module.finrank K (tripleCompleteIntersectionComponent p q r n) ≤ 12) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  by_contra hnot
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨s, hs, hker⟩ := arbitrarily_high_degree_kernel_of_not_regular
    p q r hp hq hr hp0 hrel hnot (max N 5)
  have hs5 : 5 ≤ s := (le_max_right N 5).trans hs
  obtain ⟨d, hsEq⟩ := Nat.le.dest hs5
  have hsEq' : d + 5 = s := by omega
  clear hsEq
  subst s
  have hker' : 0 < Module.finrank K (LinearMap.ker
      (cubicQuadricGradedMultiplication p q r hr (d + 5))) := by
    exact hker
  have hformula := cubic_two_quadrics_finrank_eq_twelve_add_kernel
    p q r hp hq hr hp0 hrel d
  have hNb : N ≤ d + 7 := by
    have hNs : N ≤ d + 5 := (le_max_left N 5).trans hs
    omega
  have hb := hN (d + 7) hNb
  omega

/-- Regularity of a cubic--quadric--quadric sequence is equivalent to the
eventual Hilbert bound by its expected length twelve. -/
theorem cubic_two_quadrics_regular_iff_eventually_finrank_le_twelve
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hrel : IsRelPrime p q) :
    (∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Module.finrank K (tripleCompleteIntersectionComponent p q r n) ≤ 12 := by
  constructor
  · intro hregular
    refine ⟨7, ?_⟩
    intro n hn
    have hdim := cubic_two_quadrics_hilbert_twelve
      p q r hp hq hr hp0 hq0 hrel hregular (n - 7)
    rw [Nat.sub_add_cancel hn] at hdim
    exact hdim.le
  · exact regular_of_eventually_cubic_two_quadrics_finrank_le_twelve
      p q r hp hq hr hp0 hrel

end

end PfaffianDescent
