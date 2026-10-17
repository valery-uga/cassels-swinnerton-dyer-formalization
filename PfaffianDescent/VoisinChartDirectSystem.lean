import PfaffianDescent.VoisinGenericFreenessProjectiveModel
import PfaffianDescent.VoisinFlatDirectLimit

/-!
# The graded-piece system for a projective coordinate chart

The degree-zero localization at a degree-one coordinate is built from the
homogeneous pieces by multiplication with powers of that coordinate.
-/

namespace PfaffianDescent

open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

/-- The transition from degree `i` to degree `k` in the coordinate-chart
direct system, multiplying by the coordinate to power `k - i`. -/
noncomputable def coordinatePieceTransition
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) (i k : ℕ) (hik : i ≤ k) :
    grading J i →ₗ[R] grading J k where
  toFun x := ⟨(x : CoordinateRing J) * (coordinate J j) ^ (k - i), by
    have hc : (coordinate J j) ^ (k - i) ∈ grading J (k - i) := by
      simpa using
        (SetLike.pow_mem_graded (k - i) (coordinate_mem J j))
    have hm := SetLike.mul_mem_graded x.2 hc
    rw [Nat.add_sub_of_le hik] at hm
    exact hm⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_mul]
  map_smul' r x := by
    apply Subtype.ext
    exact smul_mul_assoc r (x : CoordinateRing J) ((coordinate J j) ^ (k - i))

/-- The coordinate-power transition maps form a directed system. -/
instance coordinatePieceTransition_directedSystem
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) :
    DirectedSystem (fun n => grading J n)
      (fun i k hik => coordinatePieceTransition J v i k hik) where
  map_self := by
    intro i x
    apply Subtype.ext
    change (x : CoordinateRing J) * (coordinate J v) ^ (i - i) = x
    simp only [Nat.sub_self, pow_zero, mul_one]
  map_map := by
    intro k j i hij hjk x
    apply Subtype.ext
    change ((x : CoordinateRing J) * (coordinate J v) ^ (j - i)) *
      (coordinate J v) ^ (k - j) =
      (x : CoordinateRing J) * (coordinate J v) ^ (k - i)
    rw [mul_assoc, ← pow_add]
    have hpow : j - i + (k - j) = k - i := by omega
    rw [hpow]

/-- The graded-piece direct limit attached to a coordinate is flat whenever
the homogeneous coordinate ring is flat. -/
theorem coordinatePieceDirectLimit_flat
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (v : Fin 4) :
    Module.Flat R
      (Module.DirectLimit (fun n => grading J n)
        (fun i k hik => coordinatePieceTransition J v i k hik)) := by
  letI : ∀ n, Module.Flat R (grading J n) :=
    fun n => coordinateRing_homogeneousPiece_flat J n
  exact flat_nat_directLimit (fun i k hik => coordinatePieceTransition J v i k hik)

/-- A homogeneous degree-`n` element defines a degree-zero fraction on the
projective coordinate chart. -/
noncomputable def coordinatePieceFraction
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n : ℕ) (x : grading J n) : ChartRing J v :=
  HomogeneousLocalization.Away.mk (grading J) (coordinate_mem J v) n x.1
    (by simpa using x.2)

/-- Every element of the projective chart is a fraction from a single
homogeneous piece. -/
theorem chartRing_exists_coordinatePieceFraction
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (z : ChartRing J v) :
    ∃ n : ℕ, ∃ x : grading J n, coordinatePieceFraction J v n x = z := by
  obtain ⟨n, a, ha, hz⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading J) (coordinate_mem J v) z
  exact ⟨n, ⟨a, by simpa using ha⟩, hz⟩

/-- Passing to a later homogeneous piece does not change the represented
chart fraction. -/
theorem coordinatePieceFraction_transition
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n k : ℕ) (hnk : n ≤ k) (x : grading J n) :
    coordinatePieceFraction J v k (coordinatePieceTransition J v n k hnk x) =
      coordinatePieceFraction J v n x := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate J v))
  simp only [coordinatePieceFraction, HomogeneousLocalization.Away.val_mk]
  apply (Localization.mk_eq_mk_iff).mpr
  apply Localization.r_of_eq
  change (coordinate J v) ^ n *
      ((x : CoordinateRing J) * (coordinate J v) ^ (k - n)) =
    (coordinate J v) ^ k * (x : CoordinateRing J)
  calc
    (coordinate J v) ^ n *
        ((x : CoordinateRing J) * (coordinate J v) ^ (k - n)) =
      (coordinate J v) ^ (n + (k - n)) * (x : CoordinateRing J) := by
        rw [pow_add]
        ring
    _ = _ := by rw [Nat.add_sub_of_le hnk]

theorem coordinatePieceFraction_add
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n : ℕ) (x y : grading J n) :
    coordinatePieceFraction J v n (x + y) =
      coordinatePieceFraction J v n x + coordinatePieceFraction J v n y := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate J v))
  simp only [coordinatePieceFraction, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_add, Submodule.coe_add]
  exact (Localization.add_mk_self _ _ _).symm

/-- Scalar multiplication on a homogeneous piece agrees with the chart's
coefficient map after passing to a fraction. -/
theorem coordinatePieceFraction_smul
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n : ℕ) (r : R) (x : grading J n) :
    coordinatePieceFraction J v n (r • x) =
      chartBaseMap J v r * coordinatePieceFraction J v n x := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate J v))
  simp only [coordinatePieceFraction, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_mul, Submodule.coe_smul]
  have hbase : (chartBaseMap J v r).val =
      algebraMap R (Localization.Away (coordinate J v)) r := by
    rfl
  rw [hbase]
  simpa only [Algebra.smul_def] using
    (Localization.smul_mk (S := Submonoid.powers (coordinate J v)) r
      (x : CoordinateRing J) ⟨(coordinate J v) ^ n, ⟨n, rfl⟩⟩).symm

/-- The degree-`n` fraction map as a linear map for the chart's natural
coefficient-algebra structure. -/
noncomputable def coordinatePieceFractionLinear
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n : ℕ) :
    letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
    grading J n →ₗ[R] ChartRing J v := by
  letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
  exact {
    toFun := coordinatePieceFraction J v n
    map_add' := coordinatePieceFraction_add J v n
    map_smul' := by
      intro r x
      change coordinatePieceFraction J v n (r • x) =
        chartBaseMap J v r * coordinatePieceFraction J v n x
      exact coordinatePieceFraction_smul J v n r x }

/-- The compatible fraction maps induce a linear map from the direct limit
of homogeneous pieces to the projective chart ring. -/
noncomputable def coordinatePieceLimitToChart
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) :
    letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
    Module.DirectLimit (fun n => grading J n)
      (fun i k hik => coordinatePieceTransition J v i k hik) →ₗ[R]
        ChartRing J v := by
  letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
  apply Module.DirectLimit.lift R ℕ (fun n => grading J n)
    (fun i k hik => coordinatePieceTransition J v i k hik)
    (fun n => coordinatePieceFractionLinear J v n)
  intro i k hik x
  exact coordinatePieceFraction_transition J v i k hik x

/-- Every projective chart element is in the image of the graded-piece
direct limit. -/
theorem coordinatePieceLimitToChart_surjective
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) :
    Function.Surjective (coordinatePieceLimitToChart J v) := by
  intro z
  obtain ⟨n, x, hx⟩ := chartRing_exists_coordinatePieceFraction J v z
  refine ⟨Module.DirectLimit.of R ℕ (fun n => grading J n)
    (fun i k hik => coordinatePieceTransition J v i k hik) n x, ?_⟩
  simpa [coordinatePieceLimitToChart, coordinatePieceFractionLinear] using hx

/-- A zero chart fraction has a numerator that vanishes at a later stage
of the coordinate-power system. -/
theorem coordinatePieceFraction_zero_eventually
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) (n : ℕ) (x : grading J n)
    (hx : coordinatePieceFraction J v n x = 0) :
    ∃ k : ℕ, ∃ hnk : n ≤ k,
      coordinatePieceTransition J v n k hnk x = 0 := by
  let d : Submonoid.powers (coordinate J v) :=
    ⟨(coordinate J v) ^ n, ⟨n, rfl⟩⟩
  have hzero : Localization.mk (x : CoordinateRing J)
      d = 0 := by
    simpa only [coordinatePieceFraction, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.val_zero] using congrArg HomogeneousLocalization.val hx
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hzero
  obtain ⟨s, hs⟩ := hzero
  obtain ⟨t, ht⟩ := s.property
  refine ⟨n + t, Nat.le_add_right n t, ?_⟩
  apply Subtype.ext
  change (x : CoordinateRing J) * (coordinate J v) ^ (n + t - n) = 0
  rw [Nat.add_sub_cancel_left]
  simpa only [← ht, mul_comm] using hs

/-- The comparison from the graded-piece direct limit to the projective
chart ring is injective. -/
theorem coordinatePieceLimitToChart_injective
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) :
    Function.Injective (coordinatePieceLimitToChart J v) := by
  letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
  have hzero (z : Module.DirectLimit (fun n => grading J n)
      (fun i k hik => coordinatePieceTransition J v i k hik))
      (hz : coordinatePieceLimitToChart J v z = 0) : z = 0 := by
    obtain ⟨n, x, hx⟩ := Module.DirectLimit.exists_of z
    have hfrac : coordinatePieceFraction J v n x = 0 := by
      rw [← hx] at hz
      simpa [coordinatePieceLimitToChart, coordinatePieceFractionLinear] using hz
    obtain ⟨k, hnk, hk⟩ := coordinatePieceFraction_zero_eventually J v n x hfrac
    calc
      z = Module.DirectLimit.of R ℕ (fun n => grading J n)
          (fun i k hik => coordinatePieceTransition J v i k hik) n x := hx.symm
      _ = Module.DirectLimit.of R ℕ (fun n => grading J n)
          (fun i k hik => coordinatePieceTransition J v i k hik) k
            (coordinatePieceTransition J v n k hnk x) :=
          (Module.DirectLimit.of_f).symm
      _ = 0 := by rw [hk, map_zero]
  intro z w hzw
  have hz : coordinatePieceLimitToChart J v (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  exact sub_eq_zero.mp (hzero (z - w) hz)

/-- The degree-zero coordinate chart ring is the linear direct limit of
homogeneous pieces under multiplication by the chosen coordinate. -/
noncomputable def coordinatePieceLimitChartLinearEquiv
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    (v : Fin 4) :
    letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
    Module.DirectLimit (fun n => grading J n)
      (fun i k hik => coordinatePieceTransition J v i k hik) ≃ₗ[R]
        ChartRing J v := by
  letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
  exact LinearEquiv.ofBijective (coordinatePieceLimitToChart J v)
    ⟨coordinatePieceLimitToChart_injective J v,
      coordinatePieceLimitToChart_surjective J v⟩

/-- Flatness of a homogeneous coordinate ring implies flatness of each
actual affine projective coordinate chart ring. -/
theorem chartRing_flat_of_coordinateRing_flat
    {R : Type u} [CommRing R]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)] (v : Fin 4) :
    letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
    Module.Flat R (ChartRing J v) := by
  letI : Algebra R (ChartRing J v) := (chartBaseMap J v).toAlgebra
  letI : Module.Flat R
      (Module.DirectLimit (fun n => grading J n)
        (fun i k hik => coordinatePieceTransition J v i k hik)) :=
    coordinatePieceDirectLimit_flat J v
  exact Module.Flat.of_linearEquiv (coordinatePieceLimitChartLinearEquiv J v).symm

end PfaffianDescent
