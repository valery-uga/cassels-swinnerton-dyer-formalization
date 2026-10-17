import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Negative twists at points of Proj

For a graded commutative ring `A` and a homogeneous prime `𝔭`, the stalk of
`𝒪(-m)` is the module of homogeneous fractions whose denominator has degree
`m` more than the numerator.  This file constructs that module directly inside
the ordinary localization `A_𝔭` and proves that it is stable under the
degree-zero local ring `𝒪_{Proj A,𝔭}`.

This is the local algebra needed for the concrete `𝒪(-3)` and `𝒪(-6)` terms
in Voisin's `l = 2` restriction sequences.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveNegativeTwist

variable (𝔭 : Ideal A) [𝔭.IsPrime]

local notation "Rₚ" => Localization 𝔭.primeCompl
local notation "Rₚ₀" => HomogeneousLocalization.AtPrime 𝒜 𝔭

/-- A fraction representing a section of `𝒪(-m)` at `𝔭`: its numerator has
degree `i` and its denominator has degree `i + m`.  Zero is included
separately because a homogeneous representative of the required degree need
not exist in a degenerate grading. -/
def IsFraction (m : ℕ) (z : Rₚ) : Prop :=
  z = 0 ∨ ∃ (i : ℕ) (a : 𝒜 i) (b : 𝒜 (i + m))
    (hb : (b : A) ∈ 𝔭.primeCompl),
      z = Localization.mk (a : A) ⟨(b : A), hb⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem zero_mem (m : ℕ) : IsFraction 𝒜 𝔭 m 0 :=
  Or.inl rfl

theorem add_mem (m : ℕ) {x y : Rₚ}
    (hx : IsFraction 𝒜 𝔭 m x) (hy : IsFraction 𝒜 𝔭 m y) :
    IsFraction 𝒜 𝔭 m (x + y) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · simpa only [zero_add] using hy
  rcases hy with rfl | ⟨j, c, d, hd, rfl⟩
  · rw [add_zero]
    change
      Localization.mk (a : A) ⟨(b : A), hb⟩ = 0 ∨
        ∃ (k : ℕ) (a' : 𝒜 k) (b' : 𝒜 (k + m))
          (hb' : (b' : A) ∈ 𝔭.primeCompl),
            Localization.mk (a : A) ⟨(b : A), hb⟩ =
              Localization.mk (a' : A) ⟨(b' : A), hb'⟩
    exact Or.inr ⟨i, a, b, hb, rfl⟩
  right
  let num : 𝒜 (i + j + m) := ⟨(a : A) * d + (c : A) * b, by
    apply AddMemClass.add_mem
    · have h : (a : A) * d ∈ 𝒜 (i + (j + m)) := mul_mem_graded a.2 d.2
      simpa [add_assoc] using h
    · have h : (c : A) * b ∈ 𝒜 (j + (i + m)) := mul_mem_graded c.2 b.2
      simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 ((i + j + m) + m) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 ((i + m) + (j + m)) := mul_mem_graded b.2 d.2
    simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨i + j + m, num, den, 𝔭.primeCompl.mul_mem hb hd, ?_⟩
  simp only [num, den, Localization.add_mk]
  congr 1
  · ring

omit [GradedRing 𝒜] in
theorem neg_mem (m : ℕ) {x : Rₚ} (hx : IsFraction 𝒜 𝔭 m x) :
    IsFraction 𝒜 𝔭 m (-x) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (neg_zero)
  right
  refine ⟨i, ⟨-(a : A), NegMemClass.neg_mem a.2⟩, b, hb, ?_⟩
  exact Localization.neg_mk _ _

theorem smul_mem (m : ℕ) (r : Rₚ₀) {x : Rₚ}
    (hx : IsFraction 𝒜 𝔭 m x) :
    IsFraction 𝒜 𝔭 m (r • x) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (smul_zero r)
  obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective r
  right
  let num : 𝒜 (q.deg + i) :=
    ⟨(q.num : A) * a, mul_mem_graded q.num.2 a.2⟩
  let den : 𝒜 ((q.deg + i) + m) := ⟨(q.den : A) * b, by
    have h : (q.den : A) * b ∈ 𝒜 (q.deg + (i + m)) :=
      mul_mem_graded q.den.2 b.2
    simpa [add_assoc] using h⟩
  refine ⟨q.deg + i, num, den, 𝔭.primeCompl.mul_mem q.den_mem hb, ?_⟩
  change
    (HomogeneousLocalization.mk q : Rₚ₀).val *
        Localization.mk (a : A) ⟨(b : A), hb⟩ =
      Localization.mk ((q.num : A) * a)
        ⟨(q.den : A) * b, 𝔭.primeCompl.mul_mem q.den_mem hb⟩
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
  congr 1

/-- The stalk module of the negative twist `𝒪(-m)` at the homogeneous prime
`𝔭`, realized as a submodule of the full localization `A_𝔭`. -/
def stalkSubmodule (m : ℕ) : Submodule Rₚ₀ Rₚ where
  carrier := {z | IsFraction 𝒜 𝔭 m z}
  zero_mem' := zero_mem 𝒜 𝔭 m
  add_mem' := add_mem 𝒜 𝔭 m
  smul_mem' := smul_mem 𝒜 𝔭 m

@[simp]
theorem mem_stalkSubmodule_iff (m : ℕ) (z : Rₚ) :
    z ∈ stalkSubmodule 𝒜 𝔭 m ↔ IsFraction 𝒜 𝔭 m z :=
  Iff.rfl

/-- Equality of two fractions at a prime holds uniformly at every prime on
which one additional denominator is invertible. -/
theorem localization_eq_on_basicOpen {a b c d : A}
    (hb : b ∈ 𝔭.primeCompl) (hd : d ∈ 𝔭.primeCompl)
    (h : (Localization.mk a ⟨b, hb⟩ : Rₚ) =
      Localization.mk c ⟨d, hd⟩) :
    ∃ e : 𝔭.primeCompl,
      ∀ (q : Ideal A) [q.IsPrime]
        (hbq : b ∈ q.primeCompl) (hdq : d ∈ q.primeCompl)
        (heq : (e : A) ∈ q.primeCompl),
          (Localization.mk a ⟨b, hbq⟩ : Localization q.primeCompl) =
            Localization.mk c ⟨d, hdq⟩ := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun q _ hbq hdq heq ↦ ?_⟩
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨⟨e, heq⟩, he⟩

/-- The degree-zero homogeneous localization embeds in the concrete
degree-zero twist stalk by forgetting that its numerator and denominator have
the same degree. -/
def atPrimeToZeroTwistStalk : Rₚ₀ →ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 0 where
  toFun z := ⟨z.val, by
    right
    let b : 𝒜 (z.deg + 0) := ⟨z.den, by simpa using z.den_mem_deg⟩
    exact ⟨z.deg, ⟨z.num, z.num_mem_deg⟩, b, z.den_mem,
      z.eq_num_div_den⟩⟩
  map_add' z w := Subtype.ext (map_add (algebraMap Rₚ₀ Rₚ) z w)
  map_smul' r z := by
    apply Subtype.ext
    change (r * z).val = r.val * z.val
    exact map_mul (algebraMap Rₚ₀ Rₚ) r z

/-- Forgetting to the ordinary localization is injective on the degree-zero
homogeneous localization. -/
theorem atPrimeToZeroTwistStalk_injective :
    Function.Injective (atPrimeToZeroTwistStalk 𝒜 𝔭) := by
  intro z w h
  apply HomogeneousLocalization.val_injective 𝔭.primeCompl
  exact congr_arg Subtype.val h

/-- Every concrete degree-zero homogeneous fraction comes from the
degree-zero homogeneous localization. -/
theorem atPrimeToZeroTwistStalk_surjective :
    Function.Surjective (atPrimeToZeroTwistStalk 𝒜 𝔭) := by
  rintro ⟨z, hz⟩
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simp [atPrimeToZeroTwistStalk]
  · let b' : 𝒜 i := ⟨(b : A), by simpa using b.2⟩
    let q : Rₚ₀ := HomogeneousLocalization.mk ⟨i, a, b', hb⟩
    refine ⟨q, Subtype.ext ?_⟩
    exact HomogeneousLocalization.val_mk _

/-- The concrete stalk of `O(0)` is canonically the local ring of `Proj A`.
This does not require choosing a degree-one chart. -/
def atPrimeLinearEquivZeroTwistStalk :
    Rₚ₀ ≃ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 0 :=
  LinearEquiv.ofBijective (atPrimeToZeroTwistStalk 𝒜 𝔭)
    ⟨atPrimeToZeroTwistStalk_injective 𝒜 𝔭,
      atPrimeToZeroTwistStalk_surjective 𝒜 𝔭⟩

/-- The `m`-th power of a degree-one homogeneous element, regarded as an
element of degree `m`. -/
def degreeOnePower (f : 𝒜 1) (m : ℕ) : 𝒜 m :=
  ⟨(f : A) ^ m, by simpa using SetLike.pow_mem_graded m f.2⟩

/-- On the locus where a degree-one form `f` is invertible, the fraction
`1 / f^m` is the standard generator of the stalk of `𝒪(-m)`. -/
def localGenerator (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    stalkSubmodule 𝒜 𝔭 m := by
  let fm := degreeOnePower 𝒜 f m
  refine ⟨Localization.mk 1 ⟨(fm : A), 𝔭.primeCompl.pow_mem hf m⟩, ?_⟩
  right
  refine ⟨0, ⟨1, SetLike.one_mem_graded 𝒜⟩,
    ⟨(fm : A), by simpa only [zero_add] using fm.2⟩,
    𝔭.primeCompl.pow_mem hf m, ?_⟩
  rfl

/-- The local generator of the positive inverse twist, viewed in the full
localization.  The positive twist sheaf is constructed separately; this
element is the stalkwise inverse of the negative-twist generator. -/
def localPositiveGenerator (f : 𝒜 1) (m : ℕ) : Rₚ :=
  algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A)

/-- On the degree-one chart of `f`, the standard generators of `O(m)` and
`O(-m)` multiply to one in the ambient local ring.  This is the local
calculation needed to assemble the tensor-inverse identification for the
projective twists used in Voisin's Serre construction. -/
theorem localPositiveGenerator_mul_localGenerator
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    localPositiveGenerator 𝒜 𝔭 f m *
      (localGenerator 𝒜 𝔭 f hf m).1 = 1 := by
  change algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) *
      Localization.mk 1
        ⟨((degreeOnePower 𝒜 f m : 𝒜 m) : A), by
          simpa [degreeOnePower] using 𝔭.primeCompl.pow_mem hf m⟩ = 1
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk']
  simp [degreeOnePower]

/-- The same generator identity in the opposite multiplication order. -/
theorem localGenerator_mul_localPositiveGenerator
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    (localGenerator 𝒜 𝔭 f hf m).1 *
      localPositiveGenerator 𝒜 𝔭 f m = 1 := by
  rw [mul_comm]
  exact localPositiveGenerator_mul_localGenerator 𝒜 𝔭 f hf m

/-- A fraction representing a local section of the positive twist `O(m)`.
Its numerator has degree `m` more than its denominator.  This is dual to
`IsFraction`, which represents the negative twist. -/
def IsPositiveFraction (m : ℕ) (z : Rₚ) : Prop :=
  z = 0 ∨ ∃ (i : ℕ) (a : 𝒜 (m + i)) (b : 𝒜 i)
    (hb : (b : A) ∈ 𝔭.primeCompl),
      z = Localization.mk (a : A) ⟨(b : A), hb⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem positiveFraction_zero_mem (m : ℕ) : IsPositiveFraction 𝒜 𝔭 m 0 :=
  Or.inl rfl

theorem positiveFraction_add_mem (m : ℕ) {x y : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x)
    (hy : IsPositiveFraction 𝒜 𝔭 m y) :
    IsPositiveFraction 𝒜 𝔭 m (x + y) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · simpa only [zero_add] using hy
  rcases hy with rfl | ⟨j, c, d, hd, rfl⟩
  · rw [add_zero]
    exact Or.inr ⟨i, a, b, hb, rfl⟩
  right
  let num : 𝒜 (m + (i + j)) :=
    ⟨(a : A) * d + (c : A) * b, by
      apply AddMemClass.add_mem
      · have h : (a : A) * d ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 d.2
        simpa only [add_assoc, add_left_comm, add_comm] using h
      · have h : (c : A) * b ∈ 𝒜 ((m + j) + i) := mul_mem_graded c.2 b.2
        simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 (i + j) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + j) := mul_mem_graded b.2 d.2
    simpa only [add_assoc] using h⟩
  refine ⟨i + j, num, den, 𝔭.primeCompl.mul_mem hb hd, ?_⟩
  simp only [num, den, Localization.add_mk]
  congr 1
  ring

omit [GradedRing 𝒜] in
theorem positiveFraction_neg_mem (m : ℕ) {x : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x) :
    IsPositiveFraction 𝒜 𝔭 m (-x) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (neg_zero)
  right
  refine ⟨i, ⟨-(a : A), NegMemClass.neg_mem a.2⟩, b, hb, ?_⟩
  exact Localization.neg_mk _ _

theorem positiveFraction_smul_mem (m : ℕ) (r : Rₚ₀) {x : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x) :
    IsPositiveFraction 𝒜 𝔭 m (r • x) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (smul_zero r)
  obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective r
  right
  let num : 𝒜 (m + (q.deg + i)) :=
    ⟨(q.num : A) * a, by
      have h : (q.num : A) * a ∈ 𝒜 (q.deg + (m + i)) :=
        mul_mem_graded q.num.2 a.2
      simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 (q.deg + i) := ⟨(q.den : A) * b, by
    have h : (q.den : A) * b ∈ 𝒜 (q.deg + i) :=
      mul_mem_graded q.den.2 b.2
    simpa only [add_assoc] using h⟩
  refine ⟨q.deg + i, num, den, 𝔭.primeCompl.mul_mem q.den_mem hb, ?_⟩
  change
    (HomogeneousLocalization.mk q : Rₚ₀).val *
        Localization.mk (a : A) ⟨(b : A), hb⟩ =
      Localization.mk ((q.num : A) * a)
        ⟨(q.den : A) * b, 𝔭.primeCompl.mul_mem q.den_mem hb⟩
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
  congr 1

/-- The positive local twist module inside the full localization. -/
def positiveStalkSubmodule (m : ℕ) : Submodule Rₚ₀ Rₚ where
  carrier := {z | IsPositiveFraction 𝒜 𝔭 m z}
  zero_mem' := positiveFraction_zero_mem 𝒜 𝔭 m
  add_mem' := positiveFraction_add_mem 𝒜 𝔭 m
  smul_mem' := positiveFraction_smul_mem 𝒜 𝔭 m

@[simp]
theorem mem_positiveStalkSubmodule_iff (m : ℕ) (z : Rₚ) :
    z ∈ positiveStalkSubmodule 𝒜 𝔭 m ↔ IsPositiveFraction 𝒜 𝔭 m z :=
  Iff.rfl

/-- The positive generator `f^m` as an element of the positive local twist
module. -/
def positiveLocalGenerator (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    positiveStalkSubmodule 𝒜 𝔭 m := by
  refine ⟨localPositiveGenerator 𝒜 𝔭 f m, ?_⟩
  right
  refine ⟨0, degreeOnePower 𝒜 f m,
    ⟨1, SetLike.one_mem_graded 𝒜⟩, 𝔭.primeCompl.one_mem, ?_⟩
  symm
  dsimp [localPositiveGenerator]
  rw [Localization.mk_eq_mk']
  letI : IsLocalization 𝔭.primeCompl Rₚ := Localization.isLocalization
  exact IsLocalization.mk'_one Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A)

/-- Multiplication by the positive local generator. -/
def positiveLocalGeneratorLinearMap (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Rₚ₀ →ₗ[Rₚ₀] positiveStalkSubmodule 𝒜 𝔭 m :=
  LinearMap.toSpanSingleton Rₚ₀ _ (positiveLocalGenerator 𝒜 𝔭 f hf m)

/-- Multiplication by `f^m` is injective on the degree-zero local ring of
the basic open where `f` is invertible. -/
theorem positiveLocalGeneratorLinearMap_injective (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Injective (positiveLocalGeneratorLinearMap 𝒜 𝔭 f hf m) := by
  intro r s hrs
  apply HomogeneousLocalization.val_injective
  have h := congr_arg Subtype.val hrs
  change r.val * algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) =
      s.val * algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) at h
  have hunit : IsUnit
      (algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A)) := by
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk']
    exact (IsLocalization.AtPrime.isUnit_mk'_iff Rₚ 𝔭 _ 1).2
      (by simpa [degreeOnePower] using 𝔭.primeCompl.pow_mem hf m)
  exact hunit.mul_right_cancel h

/-- Every positive homogeneous fraction at a point of `D₊(f)` is a unique
degree-zero scalar multiple of `f^m`. -/
theorem positiveLocalGeneratorLinearMap_surjective (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Surjective (positiveLocalGeneratorLinearMap 𝒜 𝔭 f hf m) := by
  rintro ⟨z, hz⟩
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · refine ⟨0, ?_⟩
    calc
      (positiveLocalGeneratorLinearMap 𝒜 𝔭 f hf m) 0 = 0 :=
        map_zero (positiveLocalGeneratorLinearMap 𝒜 𝔭 f hf m)
      _ = ⟨0, positiveFraction_zero_mem 𝒜 𝔭 m⟩ := Subtype.ext rfl
  · let fm := degreeOnePower 𝒜 f m
    have hfm : (fm : A) ∈ 𝔭.primeCompl := by
      change (f : A) ^ m ∈ 𝔭.primeCompl
      exact 𝔭.primeCompl.pow_mem hf m
    let q : Rₚ₀ := HomogeneousLocalization.mk
      { deg := m + i
        num := a
        den := ⟨(b : A) * fm, by
          have h : (b : A) * fm ∈ 𝒜 (i + m) := mul_mem_graded b.2 fm.2
          simpa only [add_comm] using h⟩
        den_mem := 𝔭.primeCompl.mul_mem hb hfm }
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change q.val * algebraMap A Rₚ (fm : A) =
      Localization.mk (a : A) ⟨(b : A), hb⟩
    rw [show q.val = Localization.mk (a : A)
      ⟨(b : A) * fm, 𝔭.primeCompl.mul_mem hb hfm⟩ by rfl,
      ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, mul_one]
    ring

/-- The positive local twist is free of rank one on every degree-one chart. -/
def positiveLocalTrivialization (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Rₚ₀ ≃ₗ[Rₚ₀] positiveStalkSubmodule 𝒜 𝔭 m :=
  LinearEquiv.ofBijective (positiveLocalGeneratorLinearMap 𝒜 𝔭 f hf m)
    ⟨positiveLocalGeneratorLinearMap_injective 𝒜 𝔭 f hf m,
      positiveLocalGeneratorLinearMap_surjective 𝒜 𝔭 f hf m⟩

/-- A positive and a negative homogeneous fraction of the same twist degree
multiply to a degree-zero homogeneous fraction.  This is the concrete
stalkwise pairing underlying `O(m) ⊗ O(-m) ≅ O`. -/
theorem positiveFraction_mul_fraction_mem_zero (m : ℕ) {x y : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x) (hy : IsFraction 𝒜 𝔭 m y) :
    IsFraction 𝒜 𝔭 0 (x * y) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · simpa only [zero_mul] using zero_mem 𝒜 𝔭 0
  rcases hy with rfl | ⟨j, c, d, hd, rfl⟩
  · simpa only [mul_zero] using zero_mem 𝒜 𝔭 0
  right
  let k := m + i + j
  let num : 𝒜 k := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    simpa only [k, add_assoc] using h⟩
  let den : 𝒜 (k + 0) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + m)) := mul_mem_graded b.2 d.2
    simpa only [k, add_zero, add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨k, num, den, 𝔭.primeCompl.mul_mem hb hd, ?_⟩
  simp only [num, den, Localization.mk_mul]
  congr 1

/-- In the concrete zero-twist stalk, the standard positive and negative
generators pair to the unit section. -/
theorem positiveLocalGenerator_mul_localGenerator_zeroTwist
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    ⟨(positiveLocalGenerator 𝒜 𝔭 f hf m) *
        (localGenerator 𝒜 𝔭 f hf m).1,
      positiveFraction_mul_fraction_mem_zero 𝒜 𝔭 m
        (positiveLocalGenerator 𝒜 𝔭 f hf m).2
        (localGenerator 𝒜 𝔭 f hf m).2⟩ =
      atPrimeToZeroTwistStalk 𝒜 𝔭 1 := by
  apply Subtype.ext
  change (positiveLocalGenerator 𝒜 𝔭 f hf m).1 *
      (localGenerator 𝒜 𝔭 f hf m).1 =
        (atPrimeToZeroTwistStalk 𝒜 𝔭 1).1
  have hpos : (positiveLocalGenerator 𝒜 𝔭 f hf m).1 =
      localPositiveGenerator 𝒜 𝔭 f m := rfl
  have hunit : (atPrimeToZeroTwistStalk 𝒜 𝔭 1).1 = 1 := by
    change (1 : Rₚ₀).val = 1
    exact map_one (algebraMap Rₚ₀ Rₚ)
  rw [hpos, hunit]
  exact localPositiveGenerator_mul_localGenerator 𝒜 𝔭 f hf m

/-- Multiplication by the standard local generator `1 / f^m`. -/
def localGeneratorLinearMap (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Rₚ₀ →ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 m :=
  LinearMap.toSpanSingleton Rₚ₀ _ (localGenerator 𝒜 𝔭 f hf m)

/-- Multiplication by `1 / f^m` is injective over the degree-zero local
ring. -/
theorem localGeneratorLinearMap_injective (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Injective (localGeneratorLinearMap 𝒜 𝔭 f hf m) := by
  intro r s hrs
  apply HomogeneousLocalization.val_injective
  have h := congr_arg Subtype.val hrs
  change
    r.val * Localization.mk 1
        ⟨(degreeOnePower 𝒜 f m : A), 𝔭.primeCompl.pow_mem hf m⟩ =
      s.val * Localization.mk 1
        ⟨(degreeOnePower 𝒜 f m : A), 𝔭.primeCompl.pow_mem hf m⟩ at h
  have hunit : IsUnit
      (Localization.mk 1
        ⟨(degreeOnePower 𝒜 f m : A), 𝔭.primeCompl.pow_mem hf m⟩ : Rₚ) := by
    rw [Localization.mk_eq_mk']
    exact (IsLocalization.AtPrime.isUnit_mk'_iff Rₚ 𝔭 1 _).2
      𝔭.primeCompl.one_mem
  exact hunit.mul_right_cancel h

/-- Every degree-`-m` homogeneous fraction at a point where `f` is
invertible is a unique degree-zero scalar multiple of `1 / f^m`. -/
theorem localGeneratorLinearMap_surjective (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Surjective (localGeneratorLinearMap 𝒜 𝔭 f hf m) := by
  rintro ⟨z, hz⟩
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · refine ⟨0, ?_⟩
    calc
      (localGeneratorLinearMap 𝒜 𝔭 f hf m) 0 = 0 :=
        map_zero (localGeneratorLinearMap 𝒜 𝔭 f hf m)
      _ = ⟨0, zero_mem 𝒜 𝔭 m⟩ := Subtype.ext rfl
  · let fm := degreeOnePower 𝒜 f m
    let q : Rₚ₀ := HomogeneousLocalization.mk
      { deg := i + m
        num := ⟨(a : A) * fm, mul_mem_graded a.2 fm.2⟩
        den := b
        den_mem := hb }
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change
      q.val * Localization.mk 1
          ⟨(fm : A), 𝔭.primeCompl.pow_mem hf m⟩ =
        Localization.mk (a : A) ⟨(b : A), hb⟩
    rw [show q.val = Localization.mk ((a : A) * fm) ⟨(b : A), hb⟩ by rfl]
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, mul_one]
    ring

/-- At every point of the degree-one basic open `D₊(f)`, the stalk of
`𝒪(-m)` is free of rank one with basis `1 / f^m`. -/
def localTrivialization (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Rₚ₀ ≃ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 m :=
  LinearEquiv.ofBijective (localGeneratorLinearMap 𝒜 𝔭 f hf m)
    ⟨localGeneratorLinearMap_injective 𝒜 𝔭 f hf m,
      localGeneratorLinearMap_surjective 𝒜 𝔭 f hf m⟩

/-- Multiplication by a homogeneous form carries degree-`-(m+d)` stalk
fractions to degree-`-m` stalk fractions. -/
theorem mulHomogeneous_mem {d : ℕ} (s : 𝒜 d) (m : ℕ) {z : Rₚ}
    (hz : IsFraction 𝒜 𝔭 (m + d) z) :
    IsFraction 𝒜 𝔭 m (algebraMap A Rₚ (s : A) * z) := by
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (mul_zero _)
  right
  let num : 𝒜 (d + i) := ⟨(s : A) * a, mul_mem_graded s.2 a.2⟩
  let den : 𝒜 ((d + i) + m) := ⟨(b : A), by
    simpa only [add_assoc, add_left_comm, add_comm] using b.2⟩
  refine ⟨d + i, num, den, hb, ?_⟩
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [den, one_mul]

/-- The stalk map induced by multiplication by a homogeneous form. -/
def mulHomogeneousStalk {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    stalkSubmodule 𝒜 𝔭 (m + d) →ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 m where
  toFun z := ⟨algebraMap A Rₚ (s : A) * z.1,
    mulHomogeneous_mem 𝒜 𝔭 s m z.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r z := by
    apply Subtype.ext
    change
      algebraMap A Rₚ (s : A) * (r.val * z.1) =
        r.val * (algebraMap A Rₚ (s : A) * z.1)
    ring

/-- In the degree-one chart `D₊(f)`, a degree-`d` form is represented by
the degree-zero regular function `s / f^d`. -/
def localEquation {d : ℕ} (s : 𝒜 d) (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) : Rₚ₀ :=
  HomogeneousLocalization.mk
    { deg := d
      num := s
      den := degreeOnePower 𝒜 f d
      den_mem := 𝔭.primeCompl.pow_mem hf d }

/-- The affine equation `s / f^d` is a unit exactly away from the
hypersurface cut out by `s`. -/
theorem localEquation_isUnit_iff {d : ℕ} (s : 𝒜 d) (f : 𝒜 1)
    (hf : (f : A) ∈ 𝔭.primeCompl) :
    IsUnit (localEquation 𝒜 𝔭 s f hf) ↔ (s : A) ∈ 𝔭.primeCompl := by
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
  change IsUnit
    (Localization.mk (s : A)
      ⟨(degreeOnePower 𝒜 f d : A), 𝔭.primeCompl.pow_mem hf d⟩ : Rₚ) ↔ _
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]

/-- Multiplication by a degree-`d` homogeneous form raises the degree of a
positive homogeneous fraction by `d`. -/
theorem mulHomogeneous_positiveFraction_mem {d : ℕ} (s : 𝒜 d) (m : ℕ)
    {z : Rₚ} (hz : IsPositiveFraction 𝒜 𝔭 m z) :
    IsPositiveFraction 𝒜 𝔭 (m + d)
      (algebraMap A Rₚ (s : A) * z) := by
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (mul_zero _)
  right
  let num : 𝒜 ((m + d) + i) := ⟨(s : A) * a, by
    have h : (s : A) * a ∈ 𝒜 (d + (m + i)) := mul_mem_graded s.2 a.2
    simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨i, num, b, hb, ?_⟩
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [one_mul]

/-- Multiplication by a homogeneous form on concrete positive-twist stalks. -/
def positiveMulHomogeneousStalk {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    positiveStalkSubmodule 𝒜 𝔭 m →ₗ[Rₚ₀]
      positiveStalkSubmodule 𝒜 𝔭 (m + d) where
  toFun z := ⟨algebraMap A Rₚ (s : A) * z.1,
    mulHomogeneous_positiveFraction_mem 𝒜 𝔭 s m z.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r z := by
    apply Subtype.ext
    change algebraMap A Rₚ (s : A) * (r.val * z.1) =
      r.val * (algebraMap A Rₚ (s : A) * z.1)
    ring

/-- In the degree-one chart `D₊(f)`, positive homogeneous multiplication is
multiplication by the ordinary local equation `s / f^d`. -/
theorem positiveMulHomogeneousStalk_localGenerator {d : ℕ} (s : 𝒜 d)
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    positiveMulHomogeneousStalk 𝒜 𝔭 s m
        (positiveLocalGenerator 𝒜 𝔭 f hf m) =
      localEquation 𝒜 𝔭 s f hf •
        positiveLocalGenerator 𝒜 𝔭 f hf (m + d) := by
  apply Subtype.ext
  change algebraMap A Rₚ (s : A) *
      algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) =
    (localEquation 𝒜 𝔭 s f hf).val *
      algebraMap A Rₚ ((degreeOnePower 𝒜 f (m + d) : 𝒜 (m + d)) : A)
  rw [← map_mul]
  conv_rhs =>
    rw [show (localEquation 𝒜 𝔭 s f hf).val =
      Localization.mk (s : A)
        ⟨(degreeOnePower 𝒜 f d : A),
          𝔭.primeCompl.pow_mem hf d⟩ by rfl,
      ← Localization.mk_one_eq_algebraMap]
  conv_lhs => rw [← Localization.mk_one_eq_algebraMap]
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, mul_one,
    degreeOnePower]
  rw [pow_add]
  ring

/-- The coordinate formula for positive homogeneous multiplication in the
standard local bases. -/
theorem positiveMulHomogeneousStalk_localTrivialization_apply {d : ℕ}
    (s : 𝒜 d) (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m : ℕ) (r : Rₚ₀) :
    positiveMulHomogeneousStalk 𝒜 𝔭 s m
        (positiveLocalTrivialization 𝒜 𝔭 f hf m r) =
      positiveLocalTrivialization 𝒜 𝔭 f hf (m + d)
        (localEquation 𝒜 𝔭 s f hf * r) := by
  change positiveMulHomogeneousStalk 𝒜 𝔭 s m
      (r • positiveLocalGenerator 𝒜 𝔭 f hf m) =
    (localEquation 𝒜 𝔭 s f hf * r) •
      positiveLocalGenerator 𝒜 𝔭 f hf (m + d)
  rw [map_smul, positiveMulHomogeneousStalk_localGenerator]
  simp only [mul_smul, mul_comm]

/-- Away from `V(s)`, homogeneous multiplication is an isomorphism on the
concrete positive-twist stalks. -/
theorem positiveMulHomogeneousStalk_bijective_of_mem_primeCompl {d : ℕ}
    (s : 𝒜 d) (hs : (s : A) ∈ 𝔭.primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Bijective (positiveMulHomogeneousStalk 𝒜 𝔭 s m) := by
  let e := localEquation 𝒜 𝔭 s f hf
  let source := positiveLocalTrivialization 𝒜 𝔭 f hf m
  let target := positiveLocalTrivialization 𝒜 𝔭 f hf (m + d)
  have he : IsUnit e := (localEquation_isUnit_iff 𝒜 𝔭 s f hf).2 hs
  constructor
  · intro z w hzw
    apply source.symm.injective
    apply he.mul_left_cancel
    apply target.injective
    rw [← positiveMulHomogeneousStalk_localTrivialization_apply,
      ← positiveMulHomogeneousStalk_localTrivialization_apply,
      source.apply_symm_apply, source.apply_symm_apply]
    exact hzw
  · intro z
    obtain ⟨r, hr⟩ :=
      (IsUnit.isUnit_iff_mulLeft_bijective.mp he).2 (target.symm z)
    have hr' : localEquation 𝒜 𝔭 s f hf * r =
        (positiveLocalTrivialization 𝒜 𝔭 f hf (m + d)).symm z := by
      simpa only [e, target] using hr
    refine ⟨source r, ?_⟩
    rw [positiveMulHomogeneousStalk_localTrivialization_apply, hr',
      (positiveLocalTrivialization 𝒜 𝔭 f hf (m + d)).apply_symm_apply]

/-- Under the standard local bases, multiplication by a homogeneous form
is multiplication by its affine equation `s / f^d`. -/
theorem mulHomogeneousStalk_localGenerator {d : ℕ} (s : 𝒜 d)
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    mulHomogeneousStalk 𝒜 𝔭 s m (localGenerator 𝒜 𝔭 f hf (m + d)) =
      localEquation 𝒜 𝔭 s f hf • localGenerator 𝒜 𝔭 f hf m := by
  apply Subtype.ext
  change
    algebraMap A Rₚ (s : A) *
        Localization.mk 1
          ⟨(degreeOnePower 𝒜 f (m + d) : A),
            𝔭.primeCompl.pow_mem hf (m + d)⟩ =
      (localEquation 𝒜 𝔭 s f hf).val *
        Localization.mk 1
          ⟨(degreeOnePower 𝒜 f m : A),
            𝔭.primeCompl.pow_mem hf m⟩
  rw [← Localization.mk_one_eq_algebraMap,
    show (localEquation 𝒜 𝔭 s f hf).val =
      Localization.mk (s : A)
        ⟨(degreeOnePower 𝒜 f d : A),
          𝔭.primeCompl.pow_mem hf d⟩ by rfl,
    Localization.mk_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, mul_one,
    degreeOnePower]
  rw [pow_add]
  ring

/-- The full coordinate formula for the stalk map in the standard
trivializations. -/
theorem mulHomogeneousStalk_localTrivialization_apply {d : ℕ}
    (s : 𝒜 d) (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m : ℕ) (r : Rₚ₀) :
    mulHomogeneousStalk 𝒜 𝔭 s m
        (localTrivialization 𝒜 𝔭 f hf (m + d) r) =
      localTrivialization 𝒜 𝔭 f hf m
        (localEquation 𝒜 𝔭 s f hf * r) := by
  change
    mulHomogeneousStalk 𝒜 𝔭 s m
        (r • localGenerator 𝒜 𝔭 f hf (m + d)) =
      (localEquation 𝒜 𝔭 s f hf * r) •
        localGenerator 𝒜 𝔭 f hf m
  rw [map_smul, mulHomogeneousStalk_localGenerator]
  simp only [mul_smul, mul_comm]

/-- Away from the hypersurface `V(s)`, multiplication by `s` is an
isomorphism on every negative-twist stalk.  Consequently its cokernel is
supported on `V(s)`. -/
theorem mulHomogeneousStalk_bijective_of_mem_primeCompl {d : ℕ}
    (s : 𝒜 d) (hs : (s : A) ∈ 𝔭.primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl) (m : ℕ) :
    Function.Bijective (mulHomogeneousStalk 𝒜 𝔭 s m) := by
  let e := localEquation 𝒜 𝔭 s f hf
  let source := localTrivialization 𝒜 𝔭 f hf (m + d)
  let target := localTrivialization 𝒜 𝔭 f hf m
  have he : IsUnit e := (localEquation_isUnit_iff 𝒜 𝔭 s f hf).2 hs
  constructor
  · intro z w hzw
    apply source.symm.injective
    apply he.mul_left_cancel
    apply target.injective
    rw [← mulHomogeneousStalk_localTrivialization_apply,
      ← mulHomogeneousStalk_localTrivialization_apply,
      source.apply_symm_apply, source.apply_symm_apply]
    exact hzw
  · intro z
    obtain ⟨r, hr⟩ :=
      (IsUnit.isUnit_iff_mulLeft_bijective.mp he).2 (target.symm z)
    have hr' : localEquation 𝒜 𝔭 s f hf * r =
        (localTrivialization 𝒜 𝔭 f hf m).symm z := by
      simpa only [e, target] using hr
    refine ⟨source r, ?_⟩
    rw [mulHomogeneousStalk_localTrivialization_apply, hr',
      (localTrivialization 𝒜 𝔭 f hf m).apply_symm_apply]

section Sheaf

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- The underlying prime ideal of a point of `Proj A`. -/
abbrev pointIdeal (x : X) : Ideal A :=
  HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)

instance pointIdealIsPrime (x : X) : (pointIdeal 𝒜 x).IsPrime :=
  ProjectiveSpectrum.isPrime x

/-- The ambient fiber in which the stalk of a negative twist is realized. -/
abbrev Fiber (x : X) : Type u :=
  Localization (pointIdeal 𝒜 x).primeCompl

/-- A function on an open of `Proj A` is a fixed homogeneous fraction of
degree `-m`.  The separate zero case makes this predicate valid without any
generation hypothesis on the grading. -/
def IsSectionFraction (m : ℕ) {U : Opens X} (f : ∀ x : U, Fiber 𝒜 x.1) : Prop :=
  f = 0 ∨ ∃ (i : ℕ) (a : 𝒜 i) (b : 𝒜 (i + m))
    (hb : ∀ x : U, (b : A) ∈
      (pointIdeal 𝒜 x.1).primeCompl),
      ∀ x : U, f x = Localization.mk (a : A) ⟨(b : A), hb x⟩

/-- Two fixed homogeneous-fraction sections which have the same value at a
point agree on a smaller open neighborhood of that point. -/
theorem isSectionFraction_eq_neighborhood (m : ℕ)
    {U V : Opens X} {f : ∀ y : U, Fiber 𝒜 y.1}
    {g : ∀ y : V, Fiber 𝒜 y.1}
    (hf : IsSectionFraction 𝒜 m f) (hg : IsSectionFraction 𝒜 m g)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hx : f ⟨x, hxU⟩ = g ⟨x, hxV⟩) :
    ∃ (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
      ∀ w : W, f (iWU w) = g (iWV w) := by
  obtain ⟨a, b, hb, hfval⟩ :
      ∃ (a b : A)
        (hb : ∀ y : U, b ∈ (pointIdeal 𝒜 y.1).primeCompl),
        ∀ y : U, f y = Localization.mk a ⟨b, hb y⟩ := by
    rcases hf with rfl | ⟨i, a, b, hb, hval⟩
    · exact ⟨0, 1, fun _ ↦ Submonoid.one_mem _,
        fun _ ↦ (Localization.mk_zero _).symm⟩
    · exact ⟨a, b, hb, hval⟩
  obtain ⟨c, d, hd, hgval⟩ :
      ∃ (c d : A)
        (hd : ∀ y : V, d ∈ (pointIdeal 𝒜 y.1).primeCompl),
        ∀ y : V, g y = Localization.mk c ⟨d, hd y⟩ := by
    rcases hg with rfl | ⟨i, c, d, hd, hval⟩
    · exact ⟨0, 1, fun _ ↦ Submonoid.one_mem _,
        fun _ ↦ (Localization.mk_zero _).symm⟩
    · exact ⟨c, d, hd, hval⟩
  rw [hfval, hgval] at hx
  obtain ⟨e, he⟩ := localization_eq_on_basicOpen
    (pointIdeal 𝒜 x) (hb ⟨x, hxU⟩) (hd ⟨x, hxV⟩) hx
  let B := ProjectiveSpectrum.basicOpen 𝒜 (e : A)
  let W := (U ⊓ V) ⊓ B
  have hxB : x ∈ B := by
    change (e : A) ∉ x.asHomogeneousIdeal
    exact e.2
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxB⟩
  let iWU : W ⟶ U := Opens.infLELeft (U ⊓ V) B ≫ Opens.infLELeft U V
  let iWV : W ⟶ V := Opens.infLELeft (U ⊓ V) B ≫ Opens.infLERight U V
  refine ⟨W, hxW, iWU, iWV, fun w ↦ ?_⟩
  rw [hfval, hgval]
  apply he (pointIdeal 𝒜 w.1)
  rw [Ideal.mem_primeCompl_iff]
  have hwB : w.1 ∈ ProjectiveSpectrum.basicOpen 𝒜 (e : A) := w.2.2
  exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (e : A) w.1).mp hwB

/-- The fixed-fraction condition is stable under restriction. -/
def isSectionFractionPrelocal (m : ℕ) : PrelocalPredicate (Fiber 𝒜) where
  pred f := IsSectionFraction 𝒜 m f
  res := by
    rintro U V i f (rfl | ⟨j, a, b, hb, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨j, a, b, fun x ↦ hb (i x), fun x ↦ h (i x)⟩

/-- The local fixed-fraction predicate defining the negative twist. -/
def isLocallySectionFraction (m : ℕ) : LocalPredicate (Fiber 𝒜) :=
  (isSectionFractionPrelocal 𝒜 m).sheafify

/-- Two locally homogeneous-fraction sections which agree at a point agree
on a neighborhood of that point. -/
theorem isLocallySectionFraction_eq_neighborhood (m : ℕ)
    {U V : Opens X} {f : ∀ y : U, Fiber 𝒜 y.1}
    {g : ∀ y : V, Fiber 𝒜 y.1}
    (hf : (isLocallySectionFraction 𝒜 m).pred f)
    (hg : (isLocallySectionFraction 𝒜 m).pred g)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hx : f ⟨x, hxU⟩ = g ⟨x, hxV⟩) :
    ∃ (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
      ∀ w : W, f (iWU w) = g (iWV w) := by
  rcases hf ⟨x, hxU⟩ with ⟨U', hxU', iU, hf'⟩
  rcases hg ⟨x, hxV⟩ with ⟨V', hxV', iV, hg'⟩
  have hx' :
      f (iU ⟨x, hxU'⟩) = g (iV ⟨x, hxV'⟩) := by
    simpa using hx
  obtain ⟨W, hxW, iWU', iWV', hW⟩ :=
    isSectionFraction_eq_neighborhood 𝒜 m hf' hg' x hxU' hxV' hx'
  refine ⟨W, hxW, iWU' ≫ iU, iWV' ≫ iV, fun w ↦ ?_⟩
  exact hW w

theorem isSectionFraction_zero (m : ℕ) {U : Opens X} :
    IsSectionFraction 𝒜 m (0 : ∀ x : U, Fiber 𝒜 x.1) :=
  Or.inl rfl

theorem isSectionFraction_add (m : ℕ) {U : Opens X}
    {f g : ∀ x : U, Fiber 𝒜 x.1}
    (hf : IsSectionFraction 𝒜 m f) (hg : IsSectionFraction 𝒜 m g) :
    IsSectionFraction 𝒜 m (f + g) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · simpa only [zero_add] using hg
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · rw [add_zero]
    exact Or.inr ⟨i, a, b, hb, hf⟩
  right
  let num : 𝒜 (i + j + m) := ⟨(a : A) * d + (c : A) * b, by
    apply AddMemClass.add_mem
    · have h : (a : A) * d ∈ 𝒜 (i + (j + m)) := mul_mem_graded a.2 d.2
      simpa only [add_assoc] using h
    · have h : (c : A) * b ∈ 𝒜 (j + (i + m)) := mul_mem_graded c.2 b.2
      simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 ((i + j + m) + m) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 ((i + m) + (j + m)) := mul_mem_graded b.2 d.2
    simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨i + j + m, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · rw [Pi.add_apply, hf x, hg x, Localization.add_mk]
    congr 1
    ring

theorem isSectionFraction_neg (m : ℕ) {U : Opens X}
    {f : ∀ x : U, Fiber 𝒜 x.1} (hf : IsSectionFraction 𝒜 m f) :
    IsSectionFraction 𝒜 m (-f) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (neg_zero)
  right
  refine ⟨i, ⟨-(a : A), NegMemClass.neg_mem a.2⟩, b, hb, fun x ↦ ?_⟩
  rw [Pi.neg_apply, hf x]
  exact Localization.neg_mk _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplying a degree-zero fixed fraction by a degree-`-m` fixed fraction
again gives a degree-`-m` fixed fraction. -/
theorem isSectionFraction_smul (m : ℕ) {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜
      (pointIdeal 𝒜 x.1)}
    {f : ∀ x : U, Fiber 𝒜 x.1}
    (hr : ProjectiveSpectrum.StructureSheaf.IsFraction r)
    (hf : IsSectionFraction 𝒜 m f) :
    IsSectionFraction 𝒜 m (fun x ↦ r x • f x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ smul_zero (r x))
  rcases hr with ⟨j, c, d, hd, hr⟩
  right
  let num : 𝒜 (j + i) := ⟨(c : A) * a, mul_mem_graded c.2 a.2⟩
  let den : 𝒜 ((j + i) + m) := ⟨(d : A) * b, by
    have h : (d : A) * b ∈ 𝒜 (j + (i + m)) := mul_mem_graded d.2 b.2
    simpa only [add_assoc] using h⟩
  refine ⟨j + i, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hd x) (hb x)
  · change r x • f x = _
    rw [hr x, hf x]
    change
      (HomogeneousLocalization.mk _).val * Localization.mk (a : A) _ =
        Localization.mk ((c : A) * a) _
    rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
    congr 1

theorem isLocallySectionFraction_zero (m : ℕ) {U : Opens X} :
    (isLocallySectionFraction 𝒜 m).pred
      (0 : ∀ x : U, Fiber 𝒜 x.1) :=
  (isSectionFractionPrelocal 𝒜 m).sheafifyOf
    (isSectionFraction_zero 𝒜 m)

theorem isLocallySectionFraction_add (m : ℕ) {U : Opens X}
    {f g : ∀ x : U, Fiber 𝒜 x.1}
    (hf : (isLocallySectionFraction 𝒜 m).pred f)
    (hg : (isLocallySectionFraction 𝒜 m).pred g) :
    (isLocallySectionFraction 𝒜 m).pred (f + g) :=
  (isSectionFractionPrelocal 𝒜 m).sheafify_inductionOn₂'
    (isSectionFractionPrelocal 𝒜 m) (isSectionFractionPrelocal 𝒜 m)
    (fun a b ↦ a + b)
    (fun {U V} {a b} ha hb ↦
      isSectionFraction_add 𝒜 m
        ((isSectionFractionPrelocal 𝒜 m).res (Opens.infLELeft U V) a ha)
        ((isSectionFractionPrelocal 𝒜 m).res (Opens.infLERight U V) b hb)) hf hg

theorem isLocallySectionFraction_neg (m : ℕ) {U : Opens X}
    {f : ∀ x : U, Fiber 𝒜 x.1}
    (hf : (isLocallySectionFraction 𝒜 m).pred f) :
    (isLocallySectionFraction 𝒜 m).pred (-f) :=
  (isSectionFractionPrelocal 𝒜 m).sheafify_inductionOn'
    (fun a ↦ -a) (fun ha ↦ isSectionFraction_neg 𝒜 m ha) hf

set_option backward.isDefEq.respectTransparency.types false in
theorem isLocallySectionFraction_smul (m : ℕ) {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 (pointIdeal 𝒜 x.1)}
    {f : ∀ x : U, Fiber 𝒜 x.1}
    (hr : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred r)
    (hf : (isLocallySectionFraction 𝒜 m).pred f) :
    (isLocallySectionFraction 𝒜 m).pred (fun x ↦ r x • f x) :=
  (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜).sheafify_inductionOn₂'
    (isSectionFractionPrelocal 𝒜 m) (isSectionFractionPrelocal 𝒜 m)
    (fun a b ↦ a • b)
    (fun {U V} {a b} ha hb ↦
      isSectionFraction_smul 𝒜 m
        ((ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜).res
          (Opens.infLELeft U V) a ha)
        ((isSectionFractionPrelocal 𝒜 m).res (Opens.infLERight U V) b hb)) hr hf

/-- Multiplication by a homogeneous element of degree `d` sends a fixed
degree-`-(m+d)` fraction to a fixed degree-`-m` fraction. -/
theorem isSectionFraction_mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ)
    {U : Opens X} {f : ∀ x : U, Fiber 𝒜 x.1}
    (hf : IsSectionFraction 𝒜 (m + d) f) :
    IsSectionFraction 𝒜 m
      (fun x ↦ algebraMap A (Fiber 𝒜 x.1) (s : A) * f x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ mul_zero _)
  right
  let num : 𝒜 (d + i) := ⟨(s : A) * a, mul_mem_graded s.2 a.2⟩
  let den : 𝒜 ((d + i) + m) := ⟨(b : A), by
    simpa only [add_assoc, add_left_comm, add_comm] using b.2⟩
  refine ⟨d + i, num, den, fun x ↦ hb x, fun x ↦ ?_⟩
  change algebraMap A (Fiber 𝒜 x.1) (s : A) * f x = _
  rw [hf x, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  change (1 : A) * (b : A) = (den : A)
  simp only [den, one_mul]

/-- Multiplication by a homogeneous element preserves the corresponding
local fraction predicates. -/
theorem isLocallySectionFraction_mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ)
    {U : Opens X} {f : ∀ x : U, Fiber 𝒜 x.1}
    (hf : (isLocallySectionFraction 𝒜 (m + d)).pred f) :
    (isLocallySectionFraction 𝒜 m).pred
      (fun x ↦ algebraMap A (Fiber 𝒜 x.1) (s : A) * f x) := by
  intro x
  rcases hf x with ⟨V, hxV, i, hV⟩
  exact ⟨V, hxV, i, isSectionFraction_mulHomogeneous 𝒜 s m hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- Sections satisfying the local degree-`-m` fraction condition form a
module over the degree-zero structure-sheaf sections. -/
def sectionsSubmodule (m : ℕ) (U : Opens X) :
    Submodule (ProjectiveSpectrum.StructureSheaf.sectionsSubring (op U))
      (∀ x : U, Fiber 𝒜 x.1) where
  carrier := {f | (isLocallySectionFraction 𝒜 m).pred f}
  zero_mem' := isLocallySectionFraction_zero 𝒜 m
  add_mem' hf hg := isLocallySectionFraction_add 𝒜 m hf hg
  smul_mem' r f hf := by
    change (isLocallySectionFraction 𝒜 m).pred (fun x ↦ r.1 x • f x)
    exact isLocallySectionFraction_smul 𝒜 m r.2 hf

/-- The underlying type-valued sheaf of `𝒪(-m)` on `Proj A`. -/
def sheafInType (m : ℕ) : Sheaf (Type u) X :=
  subsheafToTypes (isLocallySectionFraction 𝒜 m)

instance sheafInTypeAddCommGroup (m : ℕ) (U : (Opens X)ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 m).1.obj U) :=
  (sectionsSubmodule 𝒜 m U.unop).toAddSubgroup.toAddCommGroup

instance sheafInTypeModule (m : ℕ) (U : (Opens X)ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sheafInType 𝒜 m).1.obj U) :=
  inferInstanceAs
    (Module (ProjectiveSpectrum.StructureSheaf.sectionsSubring U)
      (sectionsSubmodule 𝒜 m U.unop))

/-- The additive-group-valued presheaf underlying the negative twist. -/
def presheafInAddCommGrp (m : ℕ) : Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 m).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 m).1.map i
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The negative twist as a presheaf of modules over the structure sheaf of
`Proj A`. -/
def modulePresheaf (m : ℕ) : (Proj 𝒜).PresheafOfModules := by
  letI (U : (Opens (Proj 𝒜))ᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
        ((presheafInAddCommGrp 𝒜 m).obj U) := by
    change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sheafInType 𝒜 m).1.obj U)
    infer_instance
  exact PresheafOfModules.ofPresheaf (presheafInAddCommGrp 𝒜 m)
    (fun _ _ _ _ _ ↦ rfl)

/-- The sheaf of modules `𝒪_{Proj A}(-m)` obtained from locally homogeneous
fractions of degree `-m`. -/
def sheafOfModules (m : ℕ) : (Proj 𝒜).Modules where
  val := modulePresheaf 𝒜 m
  isSheaf := by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    change Presheaf.IsSheaf (sheafInType 𝒜 m).1
    exact (sheafInType 𝒜 m).2

/-- A fixed degree-zero structure-sheaf fraction is a fixed section of the
concrete zero twist after forgetting to the full localization. -/
theorem isSectionFraction_zero_of_structureSheafIsFraction
    {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 (pointIdeal 𝒜 x.1)}
    (hr : ProjectiveSpectrum.StructureSheaf.IsFraction r) :
    IsSectionFraction 𝒜 0 (fun x => (r x).val) := by
  rcases hr with ⟨i, a, b, hb, hr⟩
  right
  let b' : 𝒜 (i + 0) := ⟨(b : A), by simpa using b.2⟩
  refine ⟨i, a, b', ?_, fun x => ?_⟩
  · intro x
    rw [Ideal.mem_primeCompl_iff]
    exact hb x
  · change (r x).val = _
    rw [hr x, HomogeneousLocalization.val_mk]

/-- Every local structure-sheaf section gives a local section of the
concrete zero twist by applying the localization inclusion pointwise. -/
theorem isLocallySectionFraction_zero_of_structureSheaf
    {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜 (pointIdeal 𝒜 x.1)}
    (hr : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred r) :
    (isLocallySectionFraction 𝒜 0).pred (fun x => (r x).val) := by
  intro x
  rcases hr x with ⟨V, hxV, i, hV⟩
  exact ⟨V, hxV, i,
    isSectionFraction_zero_of_structureSheafIsFraction 𝒜 hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from the structure sheaf, regarded as its unit
module, to the concretely constructed zero twist. -/
def unitToZeroTwist :
    SheafOfModules.unit (Proj 𝒜).ringCatSheaf ⟶ sheafOfModules 𝒜 0 where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 0).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun r =>
              ⟨fun x => (r.1 x).val,
                isLocallySectionFraction_zero_of_structureSheaf 𝒜 r.2⟩
            map_add' := fun r s => by
              apply Subtype.ext
              funext x
              exact map_add (algebraMap
                (HomogeneousLocalization.AtPrime 𝒜 (pointIdeal 𝒜 x.1))
                (Fiber 𝒜 x.1)) (r.1 x) (s.1 x)
            map_smul' := fun r s => by
              apply Subtype.ext
              funext x
              change ((r.1 x) * (s.1 x)).val =
                (r.1 x).val * (s.1 x).val
              exact map_mul (algebraMap
                (HomogeneousLocalization.AtPrime 𝒜 (pointIdeal 𝒜 x.1))
                (Fiber 𝒜 x.1)) (r.1 x) (s.1 x) }
      naturality := by
        intro U V i
        ext
        rfl }

/-- Evaluation of a section of `𝒪(-m)` at a point, valued in the concrete
homogeneous-fraction stalk model. -/
def sectionValue (m : ℕ) (U : (Opens X)ᵒᵖ)
    (z : (sheafOfModules 𝒜 m).val.obj U) (x : U.unop) :
    stalkSubmodule 𝒜 (pointIdeal 𝒜 x.1) m := by
  refine ⟨z.1 x, ?_⟩
  rcases z.2 x with ⟨V, hxV, i, hV⟩
  rcases hV with hzero | ⟨j, a, b, hb, hval⟩
  · left
    simpa using congr_fun hzero ⟨x.1, hxV⟩
  · right
    refine ⟨j, a, b, ?_, ?_⟩
    · simpa using hb ⟨x.1, hxV⟩
    · simpa using hval ⟨x.1, hxV⟩

/-- The section `a / b` of `𝒪(-m)` on the basic open where its homogeneous
denominator `b` is nonvanishing. -/
def sectionInBasicOpen (m i : ℕ) (a : 𝒜 i) (b : 𝒜 (i + m)) :
    (modulePresheaf 𝒜 m).presheaf.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 (b : A))) := by
  let hb : ∀ y : ProjectiveSpectrum.basicOpen 𝒜 (b : A),
      (b : A) ∈ (pointIdeal 𝒜 y.1).primeCompl := fun y ↦ by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (b : A) y.1).mp y.2
  exact ⟨fun y ↦ Localization.mk (a : A) ⟨(b : A), hb y⟩,
    (isSectionFractionPrelocal 𝒜 m).sheafifyOf
      (Or.inr ⟨i, a, b, hb, fun _ ↦ rfl⟩)⟩

/-- Evaluation at a point as an additive map from sections to the concrete
fraction module. -/
def sectionValueAddMonoidHom (m : ℕ) (U : (Opens X)ᵒᵖ) (x : U.unop) :
    ((modulePresheaf 𝒜 m).presheaf.obj U) →+
      stalkSubmodule 𝒜 (pointIdeal 𝒜 x.1) m where
  toFun z := sectionValue 𝒜 m U z x
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' z w := by
    apply Subtype.ext
    rfl

/-- The evaluation cocone from neighborhoods of a point to the concrete
homogeneous-fraction module at that point. -/
def fractionModuleCocone (m : ℕ) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (modulePresheaf 𝒜 m).presheaf) where
  pt := AddCommGrpCat.of (stalkSubmodule 𝒜 (pointIdeal 𝒜 x) m)
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (sectionValueAddMonoidHom 𝒜 m (op (unop U).1) ⟨x, (unop U).2⟩) }

/-- Evaluation of germs identifies a morphism from the categorical stalk of
the negative-twist sheaf to its concrete homogeneous-fraction module. -/
def stalkToFractionModule (m : ℕ) (x : X) :
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (modulePresheaf 𝒜 m).presheaf x) : Type u) →+
      stalkSubmodule 𝒜 (pointIdeal 𝒜 x) m :=
  (colimit.desc _ (fractionModuleCocone 𝒜 m x)).hom

@[simp]
theorem stalkToFractionModule_germ (m : ℕ) (U : Opens X)
    (x : X) (hx : x ∈ U)
    (z : (modulePresheaf 𝒜 m).presheaf.obj (op U)) :
    stalkToFractionModule 𝒜 m x
        (TopCat.Presheaf.germ (C := AddCommGrpCat)
          (modulePresheaf 𝒜 m).presheaf U x hx z) =
      sectionValue 𝒜 m (op U) z ⟨x, hx⟩ := by
  dsimp [stalkToFractionModule, Presheaf.germ]
  exact CategoryTheory.Limits.colimit.ι_desc_apply _ _ _

/-- Evaluation is injective on the categorical stalk: two germs with the
same homogeneous-fraction value agree on a smaller neighborhood. -/
theorem stalkToFractionModule_injective (m : ℕ) (x : X) :
    Function.Injective (stalkToFractionModule 𝒜 m x) := by
  intro z w hzw
  obtain ⟨U, hxU, zU, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (modulePresheaf 𝒜 m).presheaf z
  obtain ⟨V, hxV, wV, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (modulePresheaf 𝒜 m).presheaf w
  have hz := stalkToFractionModule_germ 𝒜 m U x hxU zU
  have hw := stalkToFractionModule_germ 𝒜 m V x hxV wV
  have hsections := hz.symm.trans (hzw.trans hw)
  have hx : zU.1 ⟨x, hxU⟩ = wV.1 ⟨x, hxV⟩ :=
    congr_arg Subtype.val hsections
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    isLocallySectionFraction_eq_neighborhood 𝒜 m zU.2 wV.2 x hxU hxV hx
  apply TopCat.Presheaf.germ_ext (modulePresheaf 𝒜 m).presheaf W hxW iWU iWV
  apply Subtype.ext
  funext y
  exact hW y

/-- Every concrete homogeneous fraction is represented by the germ of its
fixed-fraction section on the denominator's basic open. -/
theorem stalkToFractionModule_surjective (m : ℕ) (x : X) :
    Function.Surjective (stalkToFractionModule 𝒜 m x) := by
  rintro ⟨z, hz⟩
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · let U : Opens X := ⊤
    have hxU : x ∈ U := trivial
    let zU : (modulePresheaf 𝒜 m).presheaf.obj (op U) := 0
    refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat)
      (modulePresheaf 𝒜 m).presheaf U x hxU zU, ?_⟩
    calc
      _ = sectionValue 𝒜 m (op U) zU ⟨x, hxU⟩ :=
        stalkToFractionModule_germ 𝒜 m U x hxU zU
      _ = ⟨0, zero_mem 𝒜 (pointIdeal 𝒜 x) m⟩ := Subtype.ext rfl
  · let U := ProjectiveSpectrum.basicOpen 𝒜 (b : A)
    have hxU : x ∈ U := by
      change (b : A) ∉ x.asHomogeneousIdeal
      exact hb
    let zU := sectionInBasicOpen 𝒜 m i a b
    refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat)
      (modulePresheaf 𝒜 m).presheaf U x hxU zU, ?_⟩
    calc
      _ = sectionValue 𝒜 m (op U) zU ⟨x, hxU⟩ :=
        stalkToFractionModule_germ 𝒜 m U x hxU zU
      _ = ⟨Localization.mk (a : A) ⟨(b : A), hb⟩,
          Or.inr ⟨i, a, b, hb, rfl⟩⟩ := Subtype.ext rfl

/-- The categorical stalk of the constructed negative-twist sheaf is
additively equivalent to its concrete homogeneous-fraction model. -/
def stalkAddEquivFractionModule (m : ℕ) (x : X) :
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (modulePresheaf 𝒜 m).presheaf x) : Type u) ≃+
      stalkSubmodule 𝒜 (pointIdeal 𝒜 x) m :=
  AddEquiv.ofBijective (stalkToFractionModule 𝒜 m x)
    ⟨stalkToFractionModule_injective 𝒜 m x,
      stalkToFractionModule_surjective 𝒜 m x⟩

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a homogeneous element `s` of degree `d`, as a morphism
`𝒪(-(m+d)) ⟶ 𝒪(-m)` on `Proj A`. -/
def mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    sheafOfModules 𝒜 (m + d) ⟶ sheafOfModules 𝒜 m where
  val :=
    { app := fun U ↦ by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 (m + d)).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 (m + d)).1.obj U)
          infer_instance
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 m).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ algebraMap A (Fiber 𝒜 x.1) (s : A) * f.1 x,
                isLocallySectionFraction_mulHomogeneous 𝒜 s m f.2⟩
            map_add' := fun f g ↦ by
              apply Subtype.ext
              funext x
              exact mul_add _ _ _
            map_smul' := fun r f ↦ by
              apply Subtype.ext
              funext x
              change
                algebraMap A (Fiber 𝒜 x.1) (s : A) *
                      ((r.1 x).val * f.1 x) =
                  (r.1 x).val *
                    (algebraMap A (Fiber 𝒜 x.1) (s : A) * f.1 x)
              ring }
      naturality := by
        intro U V i
        ext f
        rfl }

/-- The underlying morphism of additive presheaves of multiplication by a
homogeneous form. -/
def mulHomogeneousPresheaf {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    (modulePresheaf 𝒜 (m + d)).presheaf ⟶
      (modulePresheaf 𝒜 m).presheaf :=
  (PresheafOfModules.toPresheaf _).map (mulHomogeneous 𝒜 s m).val

/-- Evaluation intertwines the sheaf multiplication map with the concrete
stalk multiplication map. -/
theorem sectionValue_mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ)
    (U : (Opens X)ᵒᵖ)
    (z : (sheafOfModules 𝒜 (m + d)).val.obj U) (x : U.unop) :
    sectionValue 𝒜 m U ((mulHomogeneous 𝒜 s m).val.app U z) x =
      mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x.1) s m
        (sectionValue 𝒜 (m + d) U z x) :=
  rfl

/-- Evaluation identifies the categorical stalk map of multiplication by
`s` with multiplication on the concrete homogeneous-fraction module. -/
theorem stalkToFractionModule_stalkMap {d : ℕ} (s : 𝒜 d) (m : ℕ)
    (x : X)
    (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (modulePresheaf 𝒜 (m + d)).presheaf x)) :
    stalkToFractionModule 𝒜 m x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (mulHomogeneousPresheaf 𝒜 s m) z) =
      mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
        (stalkToFractionModule 𝒜 (m + d) x z) := by
  obtain ⟨U, hxU, zU, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (modulePresheaf 𝒜 (m + d)).presheaf z
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (mulHomogeneousPresheaf 𝒜 s m) zU
  have happ :
      (mulHomogeneousPresheaf 𝒜 s m).app (op U) zU =
        (mulHomogeneous 𝒜 s m).val.app (op U) zU :=
    PresheafOfModules.toPresheaf_map_app_apply
      (mulHomogeneous 𝒜 s m).val (op U) zU
  have hmap' :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (mulHomogeneousPresheaf 𝒜 s m)
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (modulePresheaf 𝒜 (m + d)).presheaf U x hxU zU) =
        TopCat.Presheaf.germ (C := AddCommGrpCat)
          (modulePresheaf 𝒜 m).presheaf U x hxU
            ((mulHomogeneous 𝒜 s m).val.app (op U) zU) := by
    exact hmap.trans (congr_arg
      (fun q ↦ TopCat.Presheaf.germ (C := AddCommGrpCat)
        (modulePresheaf 𝒜 m).presheaf U x hxU q) happ)
  calc
    _ = stalkToFractionModule 𝒜 m x
        (TopCat.Presheaf.germ (C := AddCommGrpCat)
          (modulePresheaf 𝒜 m).presheaf U x hxU
            ((mulHomogeneous 𝒜 s m).val.app (op U) zU)) :=
      congr_arg (stalkToFractionModule 𝒜 m x) hmap'
    _ = sectionValue 𝒜 m (op U)
        ((mulHomogeneous 𝒜 s m).val.app (op U) zU) ⟨x, hxU⟩ :=
      stalkToFractionModule_germ 𝒜 m U x hxU _
    _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
        (sectionValue 𝒜 (m + d) (op U) zU ⟨x, hxU⟩) :=
      sectionValue_mulHomogeneous 𝒜 s m (op U) zU ⟨x, hxU⟩
    _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
        (stalkToFractionModule 𝒜 (m + d) x
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (modulePresheaf 𝒜 (m + d)).presheaf U x hxU zU)) :=
      congr_arg (mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m)
        (stalkToFractionModule_germ 𝒜 (m + d) U x hxU zU).symm

/-- On a degree-one chart and away from `V(s)`, the actual categorical stalk
map induced by multiplication by `s` is bijective. -/
theorem mulHomogeneous_stalkMap_bijective_of_mem_primeCompl {d : ℕ}
    (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (pointIdeal 𝒜 x).primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ (pointIdeal 𝒜 x).primeCompl) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (mulHomogeneousPresheaf 𝒜 s m)) := by
  have hsource := stalkToFractionModule_injective 𝒜 (m + d) x
  have htarget := stalkToFractionModule_injective 𝒜 m x
  have hsourceSurj := stalkToFractionModule_surjective 𝒜 (m + d) x
  have hconcrete := mulHomogeneousStalk_bijective_of_mem_primeCompl
    𝒜 (pointIdeal 𝒜 x) s hs f hf m
  constructor
  · intro z w hzw
    apply hsource
    apply hconcrete.1
    calc
      mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
          (stalkToFractionModule 𝒜 (m + d) x z) =
        stalkToFractionModule 𝒜 m x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (mulHomogeneousPresheaf 𝒜 s m) z) :=
        (stalkToFractionModule_stalkMap 𝒜 s m x z).symm
      _ = stalkToFractionModule 𝒜 m x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (mulHomogeneousPresheaf 𝒜 s m) w) := congr_arg _ hzw
      _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
          (stalkToFractionModule 𝒜 (m + d) x w) :=
        stalkToFractionModule_stalkMap 𝒜 s m x w
  · intro z
    obtain ⟨a, ha⟩ := hconcrete.2 (stalkToFractionModule 𝒜 m x z)
    obtain ⟨w, hw⟩ := hsourceSurj a
    refine ⟨w, htarget ?_⟩
    calc
      stalkToFractionModule 𝒜 m x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (mulHomogeneousPresheaf 𝒜 s m) w) =
        mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m
          (stalkToFractionModule 𝒜 (m + d) x w) :=
        stalkToFractionModule_stalkMap 𝒜 s m x w
      _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s m a :=
        congr_arg _ hw
      _ = stalkToFractionModule 𝒜 m x z := ha

/-- Categorical form of
`mulHomogeneous_stalkMap_bijective_of_mem_primeCompl`. -/
theorem mulHomogeneous_stalkMap_isIso_of_mem_primeCompl {d : ℕ}
    (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (pointIdeal 𝒜 x).primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ (pointIdeal 𝒜 x).primeCompl) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (mulHomogeneousPresheaf 𝒜 s m)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (mulHomogeneous_stalkMap_bijective_of_mem_primeCompl
      𝒜 s m x hs f hf)

/-- If the irrelevant ideal is generated by degree-one elements, every point
of `Proj A` lies in a degree-one basic open.  This is the form of the standard
coordinate cover needed to remove the auxiliary chart choice from the stalk
calculation. -/
theorem exists_degreeOne_mem_primeCompl_of_irrelevant_le_span
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A))))
    (x : X) :
    ∃ f : 𝒜 1, (f : A) ∈ (pointIdeal 𝒜 x).primeCompl := by
  by_contra! h
  apply x.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
    x.asHomogeneousIdeal.toIdeal
  refine hspan.trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨f, rfl⟩
  change (f : A) ∈ pointIdeal 𝒜 x
  simpa only [Ideal.mem_primeCompl_iff, Classical.not_not] using h f

/-- Away from `V(s)`, multiplication by `s` is an isomorphism on every
actual sheaf stalk whenever degree one generates the irrelevant ideal. -/
theorem mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (pointIdeal 𝒜 x).primeCompl)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (mulHomogeneousPresheaf 𝒜 s m)) := by
  obtain ⟨f, hf⟩ :=
    exists_degreeOne_mem_primeCompl_of_irrelevant_le_span 𝒜 hspan x
  exact mulHomogeneous_stalkMap_isIso_of_mem_primeCompl 𝒜 s m x hs f hf

set_option backward.isDefEq.respectTransparency false in
/-- Over an integral domain, multiplication by a nonzero homogeneous form is
injective on sections of every open set. -/
theorem mulHomogeneous_app_injective [IsDomain A] {d : ℕ} (s : 𝒜 d)
    (hs : (s : A) ≠ 0) (m : ℕ) (U : (Opens (Proj 𝒜))ᵒᵖ) :
    Function.Injective ((mulHomogeneous 𝒜 s m).val.app U) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hx := congr_fun (congr_arg Subtype.val hfg) x
  apply mul_left_cancel₀ _ hx
  intro hzero
  apply hs
  apply IsLocalization.injective (Fiber 𝒜 x.1)
    (pointIdeal 𝒜 x.1).primeCompl_le_nonZeroDivisors
  simpa using hzero

/-- Over an integral domain, multiplication by a nonzero homogeneous form is
a monomorphism of negative twisting sheaves. -/
theorem mulHomogeneous_mono [IsDomain A] {d : ℕ} (s : 𝒜 d)
    (hs : (s : A) ≠ 0) (m : ℕ) :
    Mono (mulHomogeneous 𝒜 s m) := by
  apply (SheafOfModules.forget (Proj 𝒜).ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective
    (fun {U} ↦ mulHomogeneous_app_injective 𝒜 s hs m U)

/-- The canonical cokernel sequence associated to multiplication by a
homogeneous equation. -/
def homogeneousRestrictionSequence {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.mk (mulHomogeneous 𝒜 s m)
    (cokernel.π (mulHomogeneous 𝒜 s m))
    (cokernel.condition (mulHomogeneous 𝒜 s m))

/-- For a nonzero homogeneous equation over a domain, the canonical
hypersurface cokernel sequence
`0 -> O(-(m+d)) -> O(-m) -> coker -> 0` is short exact. -/
theorem homogeneousRestrictionSequence_shortExact [IsDomain A]
    {d : ℕ} (s : 𝒜 d) (hs : (s : A) ≠ 0) (m : ℕ) :
    (homogeneousRestrictionSequence 𝒜 s m).ShortExact := by
  let f := mulHomogeneous 𝒜 s m
  let _ : Mono f := mulHomogeneous_mono 𝒜 s hs m
  change (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact
  exact { exact := ShortComplex.exact_cokernel f }

end Sheaf

end ProjectiveNegativeTwist

end PfaffianDescent
