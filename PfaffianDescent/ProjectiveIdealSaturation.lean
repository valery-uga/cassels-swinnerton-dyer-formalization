import PfaffianDescent.ProjectiveIdealCancellation
import PfaffianDescent.GenericRegularSection
import PfaffianDescent.HomogeneousChartVanishing
import AllCharacteristics.HomogeneousProjectiveAmbient

/-!
# Associated-prime criterion for projective ideal membership

A section that vanishes on every relevant affine chart is in the homogeneous
ideal once one may choose a chart denominator avoiding the associated primes
of the quotient.  The theorem packages the exact algebraic part of the
scheme-to-ideal step in the net-of-quadrics lemma.
-/

namespace PfaffianDescent

open HomogeneousLocalization

section

variable {K R : Type*} [Field K] [Infinite K] [CommRing R]
  [Algebra K R] [IsNoetherianRing R]

/-- If a linear system avoids every associated prime modulo `I`, then a
polynomial whose quotient vanishes after localizing at each member of that
system already belongs to `I`. -/
theorem mem_of_localization_eq_zero_of_avoids_associatedPrimes
    (I : Ideal R) (W : Submodule K R) (F : R)
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ z ∈ W, Ideal.Quotient.mk I z ∉ P)
    (hzero : ∀ z ∈ W, algebraMap (R ⧸ I)
      (Localization (Submonoid.powers (Ideal.Quotient.mk I z)))
        (Ideal.Quotient.mk I F) = 0) : F ∈ I := by
  obtain ⟨z, hzW, hzregular⟩ :=
    exists_regular_mod_ideal_in_linear_system I W havoid
  exact mem_of_localization_eq_zero_of_quotient_nonZeroDivisor I z F
    (quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I z hzregular)
    (hzero z hzW)

/-- The chart form of `mem_of_localization_eq_zero_of_avoids_associatedPrimes`.
Here `𝒜` is a grading on the quotient by `I`; normalized degree-`n` chart
fractions of the image of `F` vanish on every member of the linear system. -/
theorem mem_of_away_mk_eq_zero_of_avoids_associatedPrimes
    (I : Ideal R) (W : Submodule K R) (𝒜 : ℕ → Submodule K (R ⧸ I))
    [GradedRing 𝒜] (F : R) (n : ℕ)
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ z ∈ W, Ideal.Quotient.mk I z ∉ P)
    (hz : ∀ z ∈ W, Ideal.Quotient.mk I z ∈ 𝒜 1)
    (hF : Ideal.Quotient.mk I F ∈ 𝒜 n)
    (hzero : ∀ z (hzW : z ∈ W), Away.mk 𝒜 (hz z hzW) n
      (Ideal.Quotient.mk I F) (by simpa using hF) = 0) : F ∈ I := by
  apply mem_of_localization_eq_zero_of_avoids_associatedPrimes I W F havoid
  intro z hzW
  exact localization_eq_zero_of_away_mk_eq_zero 𝒜 (hz z hzW) n
    (Ideal.Quotient.mk I F) hF (hzero z hzW)

end

end PfaffianDescent

namespace PfaffianDescent

section

variable {R : Type*} [CommRing R]

private lemma exists_nonzero_killed_by_of_power_kills
    (r x : R) (hx : x ≠ 0) (hpow : ∃ n : ℕ, r ^ n * x = 0) :
    ∃ (y : R) (m : ℕ), y ≠ 0 ∧ r * y = 0 ∧ y = r ^ m * x := by
  classical
  let n : ℕ := Nat.find hpow
  have hn : r ^ n * x = 0 := Nat.find_spec hpow
  have hn0 : n ≠ 0 := by
    intro hzero
    apply hx
    have : r ^ 0 * x = 0 := by simpa [n, hzero] using hn
    simpa using this
  refine ⟨r ^ (n - 1) * x, n - 1, ?_, ?_, rfl⟩
  · intro hzero
    have hle : n ≤ n - 1 := Nat.find_min' hpow (by simpa [n] using hzero)
    omega
  · calc
      r * (r ^ (n - 1) * x) = (r ^ (n - 1) * r) * x := by ring
      _ = r ^ ((n - 1) + 1) * x := by rw [pow_succ]
      _ = r ^ n * x := by rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
      _ = 0 := hn

private lemma power_kill_after_mul
    (r t x : R) (n m : ℕ) (h : r ^ n * x = 0) :
    r ^ n * (t ^ m * x) = 0 := by
  calc
    r ^ n * (t ^ m * x) = t ^ m * (r ^ n * x) := by ring
    _ = 0 := by rw [h, mul_zero]

private lemma kill_after_mul
    (r t x : R) (m : ℕ) (h : r * x = 0) :
    r * (t ^ m * x) = 0 :=
  by simpa using (power_kill_after_mul r t x 1 m (by simpa using h))

private lemma exists_nonzero_common_annihilator_of_power_kills_four
    (a b c d x : R) (hx : x ≠ 0)
    (ha : ∃ n : ℕ, a ^ n * x = 0)
    (hb : ∃ n : ℕ, b ^ n * x = 0)
    (hc : ∃ n : ℕ, c ^ n * x = 0)
    (hd : ∃ n : ℕ, d ^ n * x = 0) :
    ∃ y : R, y ≠ 0 ∧ a * y = 0 ∧ b * y = 0 ∧ c * y = 0 ∧ d * y = 0 := by
  obtain ⟨x₁, m₁, hx₁, ha₁, hx₁eq⟩ :=
    exists_nonzero_killed_by_of_power_kills a x hx ha
  have hb₁ : ∃ n : ℕ, b ^ n * x₁ = 0 := by
    obtain ⟨n, hn⟩ := hb
    refine ⟨n, ?_⟩
    rw [hx₁eq]
    exact power_kill_after_mul b a x n m₁ hn
  obtain ⟨x₂, m₂, hx₂, hb₂, hx₂eq⟩ :=
    exists_nonzero_killed_by_of_power_kills b x₁ hx₁ hb₁
  have ha₂ : a * x₂ = 0 := by
    rw [hx₂eq]
    exact kill_after_mul a b x₁ m₂ ha₁
  have hc₁ : ∃ n : ℕ, c ^ n * x₁ = 0 := by
    obtain ⟨n, hn⟩ := hc
    refine ⟨n, ?_⟩
    rw [hx₁eq]
    exact power_kill_after_mul c a x n m₁ hn
  have hc₂ : ∃ n : ℕ, c ^ n * x₂ = 0 := by
    obtain ⟨n, hn⟩ := hc₁
    refine ⟨n, ?_⟩
    rw [hx₂eq]
    exact power_kill_after_mul c b x₁ n m₂ hn
  obtain ⟨x₃, m₃, hx₃, hc₃, hx₃eq⟩ :=
    exists_nonzero_killed_by_of_power_kills c x₂ hx₂ hc₂
  have ha₃ : a * x₃ = 0 := by
    rw [hx₃eq]
    exact kill_after_mul a c x₂ m₃ ha₂
  have hb₃ : b * x₃ = 0 := by
    rw [hx₃eq]
    exact kill_after_mul b c x₂ m₃ hb₂
  have hd₁ : ∃ n : ℕ, d ^ n * x₁ = 0 := by
    obtain ⟨n, hn⟩ := hd
    refine ⟨n, ?_⟩
    rw [hx₁eq]
    exact power_kill_after_mul d a x n m₁ hn
  have hd₂ : ∃ n : ℕ, d ^ n * x₂ = 0 := by
    obtain ⟨n, hn⟩ := hd₁
    refine ⟨n, ?_⟩
    rw [hx₂eq]
    exact power_kill_after_mul d b x₁ n m₂ hn
  have hd₃ : ∃ n : ℕ, d ^ n * x₃ = 0 := by
    obtain ⟨n, hn⟩ := hd₂
    refine ⟨n, ?_⟩
    rw [hx₃eq]
    exact power_kill_after_mul d c x₂ n m₃ hn
  obtain ⟨y, m₄, hy, hd₄, hyeq⟩ :=
    exists_nonzero_killed_by_of_power_kills d x₃ hx₃ hd₃
  refine ⟨y, hy, ?_, ?_, ?_, hd₄⟩
  · rw [hyeq]
    exact kill_after_mul a d x₃ m₄ ha₃
  · rw [hyeq]
    exact kill_after_mul b d x₃ m₄ hb₃
  · rw [hyeq]
    exact kill_after_mul c d x₃ m₄ hc₃

theorem mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    (I : Ideal R) (a b c d F : R)
    (hsocle : ∀ x : R ⧸ I,
      Ideal.Quotient.mk I a * x = 0 →
      Ideal.Quotient.mk I b * x = 0 →
      Ideal.Quotient.mk I c * x = 0 →
      Ideal.Quotient.mk I d * x = 0 → x = 0)
    (hzero : ∀ z ∈ ({a, b, c, d} : Set R),
      algebraMap (R ⧸ I)
        (Localization (Submonoid.powers (Ideal.Quotient.mk I z)))
        (Ideal.Quotient.mk I F) = 0) : F ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  by_contra hF
  have ha : ∃ n : ℕ, (Ideal.Quotient.mk I a) ^ n * Ideal.Quotient.mk I F = 0 := by
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk I a)) _ (Ideal.Quotient.mk I F)).mp
        (hzero a (by simp))
    obtain ⟨n, hn⟩ := s.2
    rw [← hn] at hs
    exact ⟨n, hs⟩
  have hb : ∃ n : ℕ, (Ideal.Quotient.mk I b) ^ n * Ideal.Quotient.mk I F = 0 := by
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk I b)) _ (Ideal.Quotient.mk I F)).mp
        (hzero b (by simp))
    obtain ⟨n, hn⟩ := s.2
    rw [← hn] at hs
    exact ⟨n, hs⟩
  have hc : ∃ n : ℕ, (Ideal.Quotient.mk I c) ^ n * Ideal.Quotient.mk I F = 0 := by
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk I c)) _ (Ideal.Quotient.mk I F)).mp
        (hzero c (by simp))
    obtain ⟨n, hn⟩ := s.2
    rw [← hn] at hs
    exact ⟨n, hs⟩
  have hd : ∃ n : ℕ, (Ideal.Quotient.mk I d) ^ n * Ideal.Quotient.mk I F = 0 := by
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk I d)) _ (Ideal.Quotient.mk I F)).mp
        (hzero d (by simp))
    obtain ⟨n, hn⟩ := s.2
    rw [← hn] at hs
    exact ⟨n, hs⟩
  obtain ⟨y, hy, haya, hyb, hyc, hyd⟩ :=
    exists_nonzero_common_annihilator_of_power_kills_four
      (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b)
      (Ideal.Quotient.mk I c) (Ideal.Quotient.mk I d)
      (Ideal.Quotient.mk I F) hF ha hb hc hd
  exact hy (hsocle y haya hyb hyc hyd)


end

end PfaffianDescent

namespace PfaffianDescent

open MvPolynomial

section

variable {K : Type*} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- To avoid every associated prime, it is enough that one of the standard
projective coordinates avoids it.  This recasts the denominator condition in
the scheme-theoretic form that no associated component is supported at the
irrelevant locus. -/
theorem degreeOne_avoids_associatedPrimes_of_coordinate_avoidance
    (I : HomogeneousIdeal 𝒜)
    (hcoordinate : ∀ P ∈ associatedPrimes
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I)
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I),
      ∃ j : σ, AllCharacteristics.HomogeneousProjective.coordinate I j ∉ P) :
    ∀ P ∈ associatedPrimes
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I)
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I),
      ∃ z ∈ 𝒜 1, Ideal.Quotient.mk I.toIdeal z ∉ P := by
  intro P hP
  obtain ⟨j, hj⟩ := hcoordinate P hP
  refine ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j, ?_⟩
  change AllCharacteristics.HomogeneousProjective.coordinate I j ∉ P
  exact hj

variable [Finite σ]

/-- If no nonzero quotient class is annihilated by all standard projective
coordinates, then every associated component meets a standard chart.  This is
the socle-vanishing form of projective saturation needed for a complete
intersection. -/
theorem coordinate_avoidance_of_no_irrelevant_annihilator
    (I : HomogeneousIdeal 𝒜)
    (hsocle : ∀ x : AllCharacteristics.HomogeneousProjective.CoordinateRing I,
      (∀ j : σ, AllCharacteristics.HomogeneousProjective.coordinate I j * x = 0) → x = 0) :
    ∀ P ∈ associatedPrimes
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I)
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I),
      ∃ j : σ, AllCharacteristics.HomogeneousProjective.coordinate I j ∉ P := by
  classical
  intro P hP
  by_contra hcoordinate
  push Not at hcoordinate
  change IsAssociatedPrime P
    (AllCharacteristics.HomogeneousProjective.CoordinateRing I) at hP
  rw [isAssociatedPrime_iff] at hP
  obtain ⟨hprime, x, hPx⟩ := hP
  have hxzero : x = 0 := hsocle x (by
    intro j
    rw [hPx] at hcoordinate
    have hxmem := hcoordinate j
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hxmem
    exact hxmem)
  subst x
  apply hprime.ne_top
  rw [hPx]
  simp

/-- Socle vanishing at the irrelevant locus supplies the associated-prime
avoidance required to cancel a projectively vanishing homogeneous section. -/
theorem degreeOne_avoids_associatedPrimes_of_no_irrelevant_annihilator
    (I : HomogeneousIdeal 𝒜)
    (hsocle : ∀ x : AllCharacteristics.HomogeneousProjective.CoordinateRing I,
      (∀ j : σ, AllCharacteristics.HomogeneousProjective.coordinate I j * x = 0) → x = 0) :
    ∀ P ∈ associatedPrimes
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I)
      (AllCharacteristics.HomogeneousProjective.CoordinateRing I),
      ∃ z ∈ 𝒜 1, Ideal.Quotient.mk I.toIdeal z ∉ P :=
  degreeOne_avoids_associatedPrimes_of_coordinate_avoidance I
    (coordinate_avoidance_of_no_irrelevant_annihilator I hsocle)

end

end PfaffianDescent
