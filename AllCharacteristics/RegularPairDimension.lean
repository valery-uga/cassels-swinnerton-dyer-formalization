import AllCharacteristics.FlatPrincipalQuotient
import AllCharacteristics.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Submodule

/-!
# Dimension of a regular pair on a local surface chart

Two equations which are successively non-zero-divisors cut a
two-dimensional noetherian local ring down to dimension zero.  This is the
local algebraic input that turns the fibrewise regular coordinate condition
for the normalized Serre pencil into its zero-dimensionality conclusion on
surface charts.
-/

open scoped nonZeroDivisors
open CategoryTheory

namespace AllCharacteristics

/-- In a noetherian local ring, quotienting successively by non-zero-divisors
in the maximal ideals lowers Krull dimension by two. -/
theorem ringKrullDim_quotient_pair_add_two_of_local_nonZeroDivisors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p q : R) (hp : p ∈ R⁰) (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hqreg : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p}))) :
    ringKrullDim (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) + 2 = ringKrullDim R := by
  have hptop : Ideal.span ({p} : Set R) ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
      rw [← htop]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpmax)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_unique hle)
  let S := R ⧸ Ideal.span ({p} : Set R)
  let _ : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hptop
  let _ : IsLocalRing S := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span ({p} : Set R))) Ideal.Quotient.mk_surjective
  have hpdim : ringKrullDim S + 1 = ringKrullDim R := by
    exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      hp hpmax
  have hqmax : Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q ∈ IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hq
  have hqtop : Ideal.span ({Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q} : Set S) ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Ideal S) ≤ IsLocalRing.maximalIdeal S := by
      rw [← htop]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmax)
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_unique hle)
  let T := S ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q} : Set S)
  let _ : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hqtop
  let _ : IsLocalRing T := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q} : Set S)))
    Ideal.Quotient.mk_surjective
  have hqdim : ringKrullDim T + 1 = ringKrullDim S := by
    exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (R := S) (by simpa [S] using hqreg) hqmax
  have hqideal : Ideal.span ({Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q} : Set S) =
      (Ideal.span ({q} : Set R)).map (Ideal.Quotient.mk (Ideal.span ({p} : Set R))) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hequiv : T ≃+* R ⧸ (Ideal.span ({p} : Set R) ⊔ Ideal.span ({q} : Set R)) := by
    change S ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.span ({p} : Set R)) q} : Set S) ≃+* _
    rw [hqideal]
    exact DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({p} : Set R)) (Ideal.span ({q} : Set R))
  rw [← ringKrullDim_eq_of_ringEquiv hequiv]
  calc
    ringKrullDim T + 2 = (ringKrullDim T + 1) + 1 := by
      rw [show (2 : WithBot ℕ∞) = 1 + 1 by norm_num, ← add_assoc]
    _ = ringKrullDim S + 1 := by rw [hqdim]
    _ = ringKrullDim R := hpdim

/-- A regular pair in the maximal ideal of a two-dimensional noetherian local
ring has a zero-dimensional quotient. -/
theorem ringKrullDim_quotient_pair_eq_zero_of_local_dim_two_nonZeroDivisors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p q : R) (hp : p ∈ R⁰) (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hqreg : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R = 2) :
    ringKrullDim (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) = 0 := by
  have h := ringKrullDim_quotient_pair_add_two_of_local_nonZeroDivisors p q hp hpmax hqreg hq
  rw [hdim] at h
  apply (ENat.WithBot.add_natCast_cancel
    (a := ringKrullDim (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})))
    (b := 0) (c := 2)).mp
  simpa using h

/-- The affine zero locus of a regular pair on a two-dimensional noetherian
local chart has topological Krull dimension zero. -/
theorem topologicalKrullDim_primeSpectrum_quotient_pair_eq_zero_of_local_dim_two_nonZeroDivisors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p q : R) (hp : p ∈ R⁰) (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hqreg : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R = 2) :
    topologicalKrullDim (PrimeSpectrum (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q}))) = 0 := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_quotient_pair_eq_zero_of_local_dim_two_nonZeroDivisors
    p q hp hpmax hqreg hq hdim

/-- The quotient by a regular pair in a two-dimensional noetherian local ring
is Artinian. -/
theorem isArtinianRing_quotient_pair_of_local_dim_two_nonZeroDivisors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p q : R) (hp : p ∈ R⁰) (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hqreg : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R = 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE,
    Order.krullDimLE_iff, ← ringKrullDim, Nat.cast_zero]
  exact (ringKrullDim_quotient_pair_eq_zero_of_local_dim_two_nonZeroDivisors
    p q hp hpmax hqreg hq hdim).le

/-- Two successive non-zero-divisors already make the quotient Artinian when
the ambient local dimension is at most two.  This weaker form is the natural
one for an affine cubic chart presented as a hypersurface quotient. -/
theorem isArtinianRing_quotient_pair_of_local_dim_le_two_nonZeroDivisors
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p q : R) (hp : p ∈ R⁰) (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hqreg : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R ≤ 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE,
    Order.krullDimLE_iff, ← ringKrullDim, Nat.cast_zero]
  let T := R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})
  have h : ringKrullDim T + 2 ≤ (0 : WithBot ℕ∞) + 2 := by
    rw [ringKrullDim_quotient_pair_add_two_of_local_nonZeroDivisors p q hp hpmax hqreg hq]
    simpa using hdim
  cases hT : ringKrullDim T with
  | bot => simp
  | coe a =>
    rw [hT] at h
    have ha : a + 2 ≤ 0 + 2 := by
      exact WithBot.coe_le_coe.mp (by simpa using h)
    norm_cast
    exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp ha

/-- In a regular local ring, two successive cotangent-space parameters are
successive non-zero-divisors.  This gives the local algebraic form of a
transverse pair of section coordinates: the first coordinate is outside
`m²`, and its image has the same property in the first parameter quotient. -/
theorem local_nonZeroDivisors_of_successive_regularParameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (p q : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R)
    (hp_square : p ∉ IsLocalRing.maximalIdeal R ^ 2)
    (hq_square : Ideal.Quotient.mk (Ideal.span {p}) q ∉
      ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p}))) ^ 2) :
    p ∈ R⁰ ∧ Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰ := by
  letI : IsRegularLocalRing (R ⧸ Ideal.span {p}) :=
    isRegularLocalRing_quotient_parameter p hp hp_square
  letI : IsDomain R := isDomain_of_regularLocalRing R
  letI : IsDomain (R ⧸ Ideal.span {p}) :=
    isDomain_of_regularLocalRing (R ⧸ Ideal.span {p})
  constructor
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hpzero
    apply hp_square
    rw [hpzero]
    exact (IsLocalRing.maximalIdeal R ^ 2).zero_mem
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hqzero
    apply hq_square
    rw [hqzero]
    exact ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})) ^ 2).zero_mem

/-- Every two-dimensional regular local ring has a pair of successive regular
parameters.  The construction first chooses a parameter away from the square
of the maximal ideal, then repeats the construction in its regular quotient.
Thus both coordinates are non-zero-divisors, with no residue-field
assumption. -/
theorem exists_local_nonZeroDivisor_pair_of_regularLocal_dim_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) :
    ∃ p q : R,
      p ∈ IsLocalRing.maximalIdeal R ∧
      p ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      Ideal.Quotient.mk (Ideal.span {p}) q ∈
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})) ∧
      p ∈ R⁰ ∧
      Ideal.Quotient.mk (Ideal.span {p}) q ∈ (R ⧸ Ideal.span {p})⁰ := by
  have hdim0 : ringKrullDim R ≠ 0 := by
    rw [hdim]
    norm_num
  obtain ⟨p, hp, hp_square, _⟩ := exists_parameter_avoiding_minimal_primes hdim0
  letI : IsRegularLocalRing (R ⧸ Ideal.span {p}) :=
    isRegularLocalRing_quotient_parameter p hp hp_square
  have hquotdim : ringKrullDim (R ⧸ Ideal.span {p}) + 1 = 2 := by
    rw [ringKrullDim_quotient_parameter_add_one p hp hp_square, hdim]
  have hquotdim0 : ringKrullDim (R ⧸ Ideal.span {p}) ≠ 0 := by
    intro hz
    rw [hz] at hquotdim
    norm_num at hquotdim
  obtain ⟨qbar, hqbar, hqbar_square, _⟩ :=
    exists_parameter_avoiding_minimal_primes hquotdim0
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective qbar
  have hqmax : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})) := by
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa [hq] using hqbar
  have hq_square' : Ideal.Quotient.mk (Ideal.span {p}) q ∉
      ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p}))) ^ 2 := by
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa [hq] using hqbar_square
  obtain ⟨hpreg, hqreg⟩ :=
    local_nonZeroDivisors_of_successive_regularParameters p q hp hp_square hq_square'
  exact ⟨p, q, hp, hp_square, hqmax, hpreg, hqreg⟩

/-- The maximal ideal of a two-dimensional regular local ring has two
generators, one of which can be chosen outside its square.  This is the
two-generator ideal input for identifying the local ideal of a reduced point
on a smooth surface. -/
theorem exists_pair_span_maximalIdeal_of_regularLocal_dim_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) :
    ∃ p q : R,
      p ∈ IsLocalRing.maximalIdeal R ∧
      p ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      q ∈ IsLocalRing.maximalIdeal R ∧
      Ideal.span {p} ⊔ Ideal.span {q} = IsLocalRing.maximalIdeal R := by
  classical
  have hdim0 : ringKrullDim R ≠ 0 := by
    rw [hdim]
    norm_num
  obtain ⟨p, hp, hp_square, _⟩ := exists_parameter_avoiding_minimal_primes hdim0
  obtain ⟨s, hps, hcard, hspan⟩ := exists_minimal_generators_containing p hp hp_square
  have hcard' : s.card = 2 := by
    rw [hcard]
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal.trans hdim)
  have herase : (s.erase p).card = 1 := by
    have heq := Finset.card_erase_add_one hps
    omega
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp herase
  have hs : s = {p, q} := by
    rw [← Finset.insert_erase hps, hq]
  refine ⟨p, q, hp, hp_square, ?_, ?_⟩
  · rw [← hspan, hs]
    exact Ideal.subset_span (by simp)
  · rw [← hspan, hs, Finset.coe_insert, Finset.coe_singleton,
      Ideal.span_insert, sup_comm]

/-- A two-dimensional regular local ring admits a pair of local coordinates
whose common-zero algebra is Artinian.  This packages the parameter
construction with the regular-pair dimension calculation. -/
theorem exists_regular_parameter_pair_with_artinian_quotient_of_regularLocal_dim_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) :
    ∃ p q : R,
      p ∈ IsLocalRing.maximalIdeal R ∧
      p ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      Ideal.Quotient.mk (Ideal.span {p}) q ∈
        (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})) ∧
      p ∈ R⁰ ∧
      Ideal.Quotient.mk (Ideal.span {p}) q ∈ (R ⧸ Ideal.span {p})⁰ ∧
      IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  obtain ⟨p, q, hp, hp_square, hq, hpreg, hqreg⟩ :=
    exists_local_nonZeroDivisor_pair_of_regularLocal_dim_two hdim
  refine ⟨p, q, hp, hp_square, hq, hpreg, hqreg, ?_⟩
  exact isArtinianRing_quotient_pair_of_local_dim_two_nonZeroDivisors
    p q hpreg hp hqreg hq hdim

/-- If the second coordinate is independent from the first in the cotangent
space, then its image remains outside the square of the maximal ideal after
quotienting by the first coordinate. -/
theorem quotient_not_mem_mapped_square_of_not_mem_span_sup_square
    {R : Type*} [CommRing R] (m : Ideal R) (p q : R)
    (hq : q ∉ Ideal.span {p} ⊔ m ^ 2) :
    Ideal.Quotient.mk (Ideal.span {p}) q ∉
      (m.map (Ideal.Quotient.mk (Ideal.span {p}))) ^ 2 := by
  let I : Ideal R := Ideal.span {p}
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  intro hqmap
  apply hq
  have hqcomap : q ∈ ((m ^ 2).map π).comap π := by
    change π q ∈ (m ^ 2).map π
    simpa only [π, I, pow_two, Ideal.map_mul] using hqmap
  rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hqcomap
  simpa only [I, sup_comm] using hqcomap

/-- A let-bound form of the quotient-square criterion, useful when a local
presentation introduces the quotient map and mapped maximal ideal by lets. -/
theorem quotient_not_mem_mapped_square_of_not_mem_span_sup_square_let
    {R : Type*} [CommRing R] (m : Ideal R) (p q : R)
    (hq : q ∉ Ideal.span {p} ⊔ m ^ 2) :
    let π : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk (Ideal.span {p})
    let M : Ideal (R ⧸ Ideal.span {p}) := m.map π
    π q ∉ M ^ 2 := by
  exact quotient_not_mem_mapped_square_of_not_mem_span_sup_square m p q hq

/- A rank-two Jacobian calculation is naturally expressed as linear
   independence of the two classes in the residue-field cotangent space.
   This lemma translates that differential statement back to the ideal
   membership formulation used by the regular-pair API. -/
theorem cotangentIndependentParameters_of_linearIndependent_cotangent_classes
    {R : Type*} [CommRing R] [IsLocalRing R]
    (p q : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R)
    (hq : q ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      ![(IsLocalRing.maximalIdeal R).toCotangent ⟨p, hp⟩,
       (IsLocalRing.maximalIdeal R).toCotangent ⟨q, hq⟩]) :
    p ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      q ∉ Ideal.span {p} ⊔ IsLocalRing.maximalIdeal R ^ 2 := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hp0 : m.toCotangent ⟨p, hp⟩ ≠ 0 := by
    exact hli.ne_zero 0
  have hp_square : p ∉ m ^ 2 := by
    intro hp2
    apply hp0
    exact (m.toCotangent_eq_zero ⟨p, hp⟩).mpr hp2
  have hq_linear : q ∉ Ideal.span {p} ⊔ m ^ 2 := by
    intro hqspan
    rcases Submodule.mem_sup.mp hqspan with ⟨a, ha, z, hz, haz⟩
    have hpm : Ideal.span ({p} : Set R) ≤ m := by
      apply Ideal.span_le.mpr
      intro x hx
      simpa only [Set.mem_singleton_iff] using hx ▸ hp
    have hm2m : m ^ 2 ≤ m := Ideal.pow_le_self (by decide)
    have ha_m : a ∈ m := hpm ha
    have hz_m : z ∈ m := hm2m hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    have haeq : (⟨a, ha_m⟩ : m) = c • (⟨p, hp⟩ : m) := by
      apply Subtype.ext
      simpa [smul_eq_mul, mul_comm] using hc
    have hzzero : m.toCotangent ⟨z, hz_m⟩ = 0 :=
      (m.toCotangent_eq_zero ⟨z, hz_m⟩).mpr hz
    have hqeq : m.toCotangent ⟨q, hq⟩ =
        (algebraMap R (IsLocalRing.ResidueField R) c) •
          m.toCotangent ⟨p, hp⟩ := by
      calc
        m.toCotangent ⟨q, hq⟩ = m.toCotangent ⟨a + z, Ideal.add_mem m ha_m hz_m⟩ := by
          congr 1
          exact Subtype.ext haz.symm
        _ = m.toCotangent ((⟨a, ha_m⟩ : m) + (⟨z, hz_m⟩ : m)) := by
          congr 1
        _ = m.toCotangent ⟨a, ha_m⟩ + m.toCotangent ⟨z, hz_m⟩ := by
          rw [map_add]
        _ = m.toCotangent ⟨a, ha_m⟩ := by rw [hzzero, add_zero]
        _ = c • m.toCotangent ⟨p, hp⟩ := by rw [← map_smul, haeq]
        _ = (algebraMap R (IsLocalRing.ResidueField R) c) •
              m.toCotangent ⟨p, hp⟩ := by
          rw [IsScalarTower.algebraMap_smul]
    exact ((LinearIndependent.pair_iff' hp0).mp hli _ hqeq.symm)
  exact ⟨hp_square, hq_linear⟩

/-- Two coordinates whose cotangent classes are independent are successive
non-zero-divisors in a regular local ring.  This is the direct algebraic
bridge from a rank-two Jacobian calculation to the regular-pair condition. -/
theorem local_nonZeroDivisors_of_cotangentIndependentParameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (p q : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R)
    (hp_square : p ∉ IsLocalRing.maximalIdeal R ^ 2)
    (hlinear : q ∉ Ideal.span {p} ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    p ∈ R⁰ ∧ Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (R ⧸ Ideal.span {p})⁰ := by
  apply local_nonZeroDivisors_of_successive_regularParameters p q hp hp_square
  exact quotient_not_mem_mapped_square_of_not_mem_span_sup_square
    (IsLocalRing.maximalIdeal R) p q hlinear

/-- On a regular local surface, cotangent-space independence of two
coordinates at their common zero gives an Artinian common-zero quotient. -/
theorem isArtinianRing_quotient_pair_of_cotangentIndependentParameters_dim_le_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (p q : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R)
    (hp_square : p ∉ IsLocalRing.maximalIdeal R ^ 2)
    (hq : q ∈ IsLocalRing.maximalIdeal R)
    (hlinear : q ∉ Ideal.span {p} ⊔ IsLocalRing.maximalIdeal R ^ 2)
    (hdim : ringKrullDim R ≤ 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  obtain ⟨hpreg, hqreg⟩ :=
    local_nonZeroDivisors_of_cotangentIndependentParameters p q hp hp_square hlinear
  exact isArtinianRing_quotient_pair_of_local_dim_le_two_nonZeroDivisors
    p q hpreg hp hqreg (Ideal.mem_map_of_mem _ hq) hdim

/-- A transverse pair of local section coordinates on a regular surface
chart has Artinian common-zero algebra.  Unlike the fibrewise condition used
for flatness, this only asks for the cotangent-space calculation at the
individual local ring. -/
theorem isArtinianRing_quotient_pair_of_successive_regularParameters_dim_le_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (p q : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R)
    (hp_square : p ∉ IsLocalRing.maximalIdeal R ^ 2)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hq_square : Ideal.Quotient.mk (Ideal.span {p}) q ∉
      ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p}))) ^ 2)
    (hdim : ringKrullDim R ≤ 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  obtain ⟨hpreg, hqreg⟩ :=
    local_nonZeroDivisors_of_successive_regularParameters p q hp hp_square hq_square
  exact isArtinianRing_quotient_pair_of_local_dim_le_two_nonZeroDivisors
    p q hpreg hp hqreg hq hdim

/-- On a two-dimensional local chart over a field, the existing fibrewise
regular-pair condition directly gives a zero-dimensional coordinate quotient
at a common zero of the two coordinates. -/
theorem ringKrullDim_quotient_pair_eq_zero_of_fibrewiseRegularPair_over_field
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (φ : K →+* R) (p q : R)
    (hregular : IsFibrewiseRegularPair φ p q)
    (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R = 2) :
    ringKrullDim (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) = 0 :=
  ringKrullDim_quotient_pair_eq_zero_of_local_dim_two_nonZeroDivisors
    p q
    (hregular.first_mem_nonZeroDivisors_of_field φ p q)
    hpmax
    (hregular.second_mem_nonZeroDivisors_of_field φ p q)
    hq hdim

/-- On a two-dimensional local chart over a field, a fibrewise regular pair
has Artinian common-zero coordinate ring at every common zero. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_over_field
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (φ : K →+* R) (p q : R)
    (hregular : IsFibrewiseRegularPair φ p q)
    (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R = 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) :=
  isArtinianRing_quotient_pair_of_local_dim_two_nonZeroDivisors
    p q
    (hregular.first_mem_nonZeroDivisors_of_field φ p q)
    hpmax
    (hregular.second_mem_nonZeroDivisors_of_field φ p q)
    hq hdim

/-- The at-most-two-dimensional form of the preceding field-fibre result. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_over_field_local_dim_le_two
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (φ : K →+* R) (p q : R)
    (hregular : IsFibrewiseRegularPair φ p q)
    (hpmax : p ∈ IsLocalRing.maximalIdeal R)
    (hq : Ideal.Quotient.mk (Ideal.span {p}) q ∈
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {p})))
    (hdim : ringKrullDim R ≤ 2) :
    IsArtinianRing (R ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) :=
  isArtinianRing_quotient_pair_of_local_dim_le_two_nonZeroDivisors
    p q
    (hregular.first_mem_nonZeroDivisors_of_field φ p q)
    hpmax
    (hregular.second_mem_nonZeroDivisors_of_field φ p q)
    hq hdim

/-- After localizing a field fibre, a fibrewise regular pair cuts a
two-dimensional local chart down to an Artinian coordinate quotient at every
common zero.  The regular-sequence transport through localization is supplied
by `IsFibrewiseRegularPair.local_nonZeroDivisors_of_field_of_isLocalization`. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_localization_of_field_local_dim_two
    {K A S : Type*} [Field K] [CommRing A] [CommRing S] [Algebra A S]
    (T : Submonoid A) [IsLocalization T S]
    [IsNoetherianRing S] [IsLocalRing S]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q)
    (hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S)
    (hq : Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
      (IsLocalRing.maximalIdeal S).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap A S p})))
    (hdim : ringKrullDim S = 2) :
    IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q})) := by
  have hnonzero : algebraMap A S p ∈ S⁰ ∧
      Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
        (S ⧸ Ideal.span {algebraMap A S p})⁰ :=
    IsFibrewiseRegularPair.local_nonZeroDivisors_of_field_of_isLocalization
      (K := K) (A := A) (S := S) T φ p q hregular
  exact isArtinianRing_quotient_pair_of_local_dim_two_nonZeroDivisors
    (algebraMap A S p) (algebraMap A S q) hnonzero.1 hpmax hnonzero.2 hq hdim

/-- The localization form only needs the ambient local surface chart to have
Krull dimension at most two. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_localization_of_field_local_dim_le_two
    {K A S : Type*} [Field K] [CommRing A] [CommRing S] [Algebra A S]
    (T : Submonoid A) [IsLocalization T S]
    [IsNoetherianRing S] [IsLocalRing S]
    (φ : K →+* A) (p q : A)
    (hregular : IsFibrewiseRegularPair φ p q)
    (hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S)
    (hq : Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
      (IsLocalRing.maximalIdeal S).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap A S p})))
    (hdim : ringKrullDim S ≤ 2) :
    IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q})) := by
  have hnonzero : algebraMap A S p ∈ S⁰ ∧
      Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
        (S ⧸ Ideal.span {algebraMap A S p})⁰ :=
    IsFibrewiseRegularPair.local_nonZeroDivisors_of_field_of_isLocalization
      (K := K) (A := A) (S := S) T φ p q hregular
  exact isArtinianRing_quotient_pair_of_local_dim_le_two_nonZeroDivisors
    (algebraMap A S p) (algebraMap A S q) hnonzero.1 hpmax hnonzero.2 hq hdim

/-- Localizing an affine quotient at a prime is a quotient of the localization
of the ambient ring at the corresponding preimage prime.  This is the
canonical surjective map in the direction needed to transfer Artinianness. -/
noncomputable def localizationQuotientAtPrimeMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : Ideal (A ⧸ I)) [P.IsPrime] :
    Localization.AtPrime (P.under A) →+* Localization.AtPrime P := by
  let g : A →+* Localization.AtPrime P :=
    (algebraMap (A ⧸ I) (Localization.AtPrime P)).comp (Ideal.Quotient.mk I)
  refine IsLocalization.lift (M := (P.under A).primeCompl)
    (S := Localization.AtPrime (P.under A)) (g := g) ?_
  intro x
  apply IsLocalRing.notMem_maximalIdeal.mp
  change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I x.1) ∉
    IsLocalRing.maximalIdeal (Localization.AtPrime P)
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ P]
  change Ideal.Quotient.mk I x.1 ∉ P
  exact x.2

/-- The canonical comparison from the ambient local ring to the localized
quotient is surjective. -/
theorem localizationQuotientAtPrimeMap_surjective
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : Ideal (A ⧸ I)) [P.IsPrime] :
    Function.Surjective (localizationQuotientAtPrimeMap I P) := by
  intro z
  obtain ⟨b, s, rfl⟩ :=
    IsLocalization.exists_mk'_eq P.primeCompl z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective s.1
  let s' : P.primeCompl := ⟨Ideal.Quotient.mk I c, hc ▸ s.2⟩
  have hs : s = s' := Subtype.ext hc.symm
  rw [hs]
  have hc' : c ∉ P.under A := by
    change Ideal.Quotient.mk I c ∉ P
    exact Ideal.mem_primeCompl_iff.mp s'.2
  let sc : (P.under A).primeCompl :=
    ⟨c, Ideal.mem_primeCompl_iff.mpr hc'⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime (P.under A)) a sc, ?_⟩
  let g : A →+* Localization.AtPrime P :=
    (algebraMap (A ⧸ I) (Localization.AtPrime P)).comp (Ideal.Quotient.mk I)
  have hunit : ∀ x : (P.under A).primeCompl, IsUnit (g x.1) := by
    intro x
    apply IsLocalRing.notMem_maximalIdeal.mp
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I x.1) ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime P)
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ P]
    change Ideal.Quotient.mk I x.1 ∉ P
    exact x.2
  let u := IsUnit.liftRight (g.toMonoidHom.domRestrict (P.under A).primeCompl) hunit sc
  rw [localizationQuotientAtPrimeMap, IsLocalization.lift_mk']
  change g a * (↑(u⁻¹) : Localization.AtPrime P) =
    IsLocalization.mk' (Localization.AtPrime P) (Ideal.Quotient.mk I a) s'
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  have hu : IsUnit (u : Localization.AtPrime P) := u.isUnit
  apply IsUnit.mul_right_cancel hu
  change (↑(u⁻¹) : Localization.AtPrime P) * u = _
  rw [Units.inv_mul]
  have hden : (u : Localization.AtPrime P) =
      (algebraMap (A ⧸ I) (Localization.AtPrime P)) s'.1 := by
    change g sc.1 = _
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I c) = _
    rfl
  rw [hden, IsLocalization.mk'_spec]
  simp

/-- Artinianness descends along a surjective map of commutative rings. -/
theorem isArtinianRing_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    [IsArtinianRing R] : IsArtinianRing S := by
  letI : IsNoetherianRing S := isNoetherianRing_of_surjective R S f hf
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_iff]
  exact (ringKrullDim_le_of_surjective f hf).trans
    (Ring.krullDimLE_iff.mp (show Ring.KrullDimLE 0 R from inferInstance))

/-- A noetherian affine chart is Artinian if its local rings at all maximal
ideals are Artinian.  This is the local-to-global step needed after the
regular-pair calculation has been applied at every common zero. -/
theorem isArtinianRing_of_isArtinianRing_at_maximal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Rₚ : ∀ P : Ideal R, [P.IsMaximal] → Type*)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsArtinianRing (Rₚ P)) :
    IsArtinianRing R := by
  rw [isArtinianRing_iff_krullDimLE_zero]
  apply Ring.krullDimLE_of_isLocalization_maximal Rₚ
  intro P hP
  rw [← isArtinianRing_iff_krullDimLE_zero]
  exact h P

/-- Local transverse-parameter calculations at every common zero of two
functions make their quotient Artinian.  The hypotheses are phrased at the
maximal localizations of the ambient affine ring, so a geometric Jacobian
calculation can supply them without proving a global fibrewise regularity
condition. -/
theorem
    isArtinianRing_quotient_pair_of_successive_regularParameters_at_all_common_maximal_localizations_dim_le_two
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : A)
    (hparameters : ∀ (Q : Ideal A) [Q.IsMaximal], p ∈ Q → q ∈ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧
      algebraMap A (Localization.AtPrime Q) p ∉
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2 ∧
      Ideal.Quotient.mk (Ideal.span {algebraMap A (Localization.AtPrime Q) p})
        (algebraMap A (Localization.AtPrime Q) q) ∉
        ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map
          (Ideal.Quotient.mk
            (Ideal.span {algebraMap A (Localization.AtPrime Q) p}))) ^ 2)
    (hdim : ∀ (Q : Ideal A) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  let I : Ideal A := Ideal.span {p} ⊔ Ideal.span {q}
  apply isArtinianRing_of_isArtinianRing_at_maximal
    (fun P _ => Localization.AtPrime P)
  intro P hP
  let Q : Ideal A := P.under A
  letI : Q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hpI : p ∈ I := (le_sup_left : Ideal.span {p} ≤ I)
    (Ideal.subset_span (Set.mem_singleton p))
  have hqI : q ∈ I := (le_sup_right : Ideal.span {q} ≤ I)
    (Ideal.subset_span (Set.mem_singleton q))
  have hpQ : p ∈ Q := by
    change Ideal.Quotient.mk I p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI]
    exact P.zero_mem
  have hqQ : q ∈ Q := by
    change Ideal.Quotient.mk I q ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI]
    exact P.zero_mem
  let S := Localization.AtPrime Q
  obtain ⟨hreg, hpsquare, hqsquare⟩ := hparameters Q hpQ hqQ
  letI : IsRegularLocalRing S := hreg
  have hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hpQ
  have hqmax : algebraMap A S q ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hqQ
  have hq : Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
      (IsLocalRing.maximalIdeal S).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap A S p})) :=
    Ideal.mem_map_of_mem _ hqmax
  let J : Ideal S := Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}
  have hArt : IsArtinianRing (S ⧸ J) := by
    change IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}))
    exact isArtinianRing_quotient_pair_of_successive_regularParameters_dim_le_two
      (algebraMap A S p) (algebraMap A S q) hpmax hpsquare hq hqsquare (hdim Q)
  let f : S →+* Localization.AtPrime P := localizationQuotientAtPrimeMap I P
  have hfp : f (algebraMap A S p) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI, map_zero]
  have hfq : f (algebraMap A S q) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI, map_zero]
  have hJ : J ≤ RingHom.ker f := by
    apply sup_le
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S p)
      exact hfp
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S q)
      exact hfq
  let fbar : S ⧸ J →+* Localization.AtPrime P :=
    Ideal.Quotient.lift J f (fun x hx => show f x = 0 from hJ hx)
  have hfbar : Function.Surjective fbar := by
    intro x
    obtain ⟨y, hy⟩ := localizationQuotientAtPrimeMap_surjective I P x
    refine ⟨Ideal.Quotient.mk J y, ?_⟩
    dsimp [fbar]
    change f y = x
    exact hy
  letI : IsArtinianRing (S ⧸ J) := hArt
  exact isArtinianRing_of_surjective fbar hfbar

/-- Local rank-two cotangent calculations at every common zero of two
functions make their quotient Artinian.  This is the direct global form of
the Jacobian criterion: the second coordinate is independent from the first
modulo the square of the local maximal ideal. -/
theorem
    isArtinianRing_quotient_pair_of_cotangentIndependentParameters_at_all_common_maximal_localizations_dim_le_two
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p q : A)
    (hparameters : ∀ (Q : Ideal A) [Q.IsMaximal], p ∈ Q → q ∈ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧
      algebraMap A (Localization.AtPrime Q) p ∉
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2 ∧
      algebraMap A (Localization.AtPrime Q) q ∉
        Ideal.span {algebraMap A (Localization.AtPrime Q) p} ⊔
          IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2)
    (hdim : ∀ (Q : Ideal A) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  let I : Ideal A := Ideal.span {p} ⊔ Ideal.span {q}
  apply isArtinianRing_of_isArtinianRing_at_maximal
    (fun P _ => Localization.AtPrime P)
  intro P hP
  let Q : Ideal A := P.under A
  letI : Q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hpI : p ∈ I := (le_sup_left : Ideal.span {p} ≤ I)
    (Ideal.subset_span (Set.mem_singleton p))
  have hqI : q ∈ I := (le_sup_right : Ideal.span {q} ≤ I)
    (Ideal.subset_span (Set.mem_singleton q))
  have hpQ : p ∈ Q := by
    change Ideal.Quotient.mk I p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI]
    exact P.zero_mem
  have hqQ : q ∈ Q := by
    change Ideal.Quotient.mk I q ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI]
    exact P.zero_mem
  let S := Localization.AtPrime Q
  obtain ⟨hreg, hpsquare, hlinear⟩ := hparameters Q hpQ hqQ
  letI : IsRegularLocalRing S := hreg
  have hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hpQ
  have hqmax : algebraMap A S q ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hqQ
  let J : Ideal S := Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}
  have hArt : IsArtinianRing (S ⧸ J) := by
    change IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}))
    exact isArtinianRing_quotient_pair_of_cotangentIndependentParameters_dim_le_two
      (algebraMap A S p) (algebraMap A S q) hpmax hpsquare hqmax hlinear (hdim Q)
  let f : S →+* Localization.AtPrime P := localizationQuotientAtPrimeMap I P
  have hfp : f (algebraMap A S p) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI, map_zero]
  have hfq : f (algebraMap A S q) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI, map_zero]
  have hJ : J ≤ RingHom.ker f := by
    apply sup_le
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S p)
      exact hfp
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S q)
      exact hfq
  let fbar : S ⧸ J →+* Localization.AtPrime P :=
    Ideal.Quotient.lift J f (fun x hx => show f x = 0 from hJ hx)
  have hfbar : Function.Surjective fbar := by
    intro x
    obtain ⟨y, hy⟩ := localizationQuotientAtPrimeMap_surjective I P x
    refine ⟨Ideal.Quotient.mk J y, ?_⟩
    dsimp [fbar]
    change f y = x
    exact hy
  letI : IsArtinianRing (S ⧸ J) := hArt
  exact isArtinianRing_of_surjective fbar hfbar

/-- A fibrewise regular pair on a noetherian affine surface has an Artinian
common-zero quotient when every maximal local chart has dimension two.  This
is the local-to-global form used by actual cubic-surface fibres: the pair is
first transported through each localization, then the quotient localization
is obtained as a surjective image. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_two
    {K A : Type u} [Field K] [CommRing A] [IsNoetherianRing A]
    (φ : K →+* A) (p q : A) (hregular : IsFibrewiseRegularPair φ p q)
    (hdim : ∀ (Q : Ideal A) [Q.IsMaximal], ringKrullDim (Localization.AtPrime Q) = 2) :
    IsArtinianRing (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  let I : Ideal A := Ideal.span {p} ⊔ Ideal.span {q}
  apply isArtinianRing_of_isArtinianRing_at_maximal
    (fun P _ => Localization.AtPrime P)
  intro P hP
  let Q : Ideal A := P.under A
  letI : Q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hpI : p ∈ I := (le_sup_left : Ideal.span {p} ≤ I)
    (Ideal.subset_span (Set.mem_singleton p))
  have hqI : q ∈ I := (le_sup_right : Ideal.span {q} ≤ I)
    (Ideal.subset_span (Set.mem_singleton q))
  have hpQ : p ∈ Q := by
    change Ideal.Quotient.mk I p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI]
    exact P.zero_mem
  have hqQ : q ∈ Q := by
    change Ideal.Quotient.mk I q ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI]
    exact P.zero_mem
  let S := Localization.AtPrime Q
  letI : IsNoetherianRing S := inferInstance
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S Q
  have hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hpQ
  have hqmax : algebraMap A S q ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hqQ
  have hq : Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {algebraMap A S p})) :=
    Ideal.mem_map_of_mem _ hqmax
  let J : Ideal S := Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}
  have hArt : IsArtinianRing (S ⧸ J) := by
    change IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}))
    exact isArtinianRing_quotient_pair_of_fibrewiseRegularPair_localization_of_field_local_dim_two
      Q.primeCompl φ p q hregular hpmax hq (hdim Q)
  let f : S →+* Localization.AtPrime P := localizationQuotientAtPrimeMap I P
  have hfp : f (algebraMap A S p) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI, map_zero]
  have hfq : f (algebraMap A S q) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI, map_zero]
  have hJ : J ≤ RingHom.ker f := by
    apply sup_le
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S p)
      exact hfp
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S q)
      exact hfq
  let fbar : S ⧸ J →+* Localization.AtPrime P :=
    Ideal.Quotient.lift J f (fun x hx => show f x = 0 from hJ hx)
  have hfbar : Function.Surjective fbar := by
    intro x
    obtain ⟨y, hy⟩ := localizationQuotientAtPrimeMap_surjective I P x
    refine ⟨Ideal.Quotient.mk J y, ?_⟩
    dsimp [fbar]
    change f y = x
    exact hy
  letI : IsArtinianRing (S ⧸ J) := hArt
  exact isArtinianRing_of_surjective fbar hfbar

/-- The affine regular-pair calculation only needs every maximal local chart
of the field fibre to have Krull dimension at most two. -/
theorem isArtinianRing_quotient_pair_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_le_two
    {K A : Type u} [Field K] [CommRing A] [IsNoetherianRing A]
    (φ : K →+* A) (p q : A) (hregular : IsFibrewiseRegularPair φ p q)
    (hdim : ∀ (Q : Ideal A) [Q.IsMaximal], ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing (A ⧸ (Ideal.span {p} ⊔ Ideal.span {q})) := by
  let I : Ideal A := Ideal.span {p} ⊔ Ideal.span {q}
  apply isArtinianRing_of_isArtinianRing_at_maximal
    (fun P _ => Localization.AtPrime P)
  intro P hP
  let Q : Ideal A := P.under A
  letI : Q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hpI : p ∈ I := (le_sup_left : Ideal.span {p} ≤ I)
    (Ideal.subset_span (Set.mem_singleton p))
  have hqI : q ∈ I := (le_sup_right : Ideal.span {q} ≤ I)
    (Ideal.subset_span (Set.mem_singleton q))
  have hpQ : p ∈ Q := by
    change Ideal.Quotient.mk I p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI]
    exact P.zero_mem
  have hqQ : q ∈ Q := by
    change Ideal.Quotient.mk I q ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI]
    exact P.zero_mem
  let S := Localization.AtPrime Q
  letI : IsNoetherianRing S := inferInstance
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S Q
  have hpmax : algebraMap A S p ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hpQ
  have hqmax : algebraMap A S q ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S Q]
    exact hqQ
  have hq : Ideal.Quotient.mk (Ideal.span {algebraMap A S p}) (algebraMap A S q) ∈
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {algebraMap A S p})) :=
    Ideal.mem_map_of_mem _ hqmax
  let J : Ideal S := Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}
  have hArt : IsArtinianRing (S ⧸ J) := by
    change IsArtinianRing
      (S ⧸ (Ideal.span {algebraMap A S p} ⊔ Ideal.span {algebraMap A S q}))
    exact isArtinianRing_quotient_pair_of_fibrewiseRegularPair_localization_of_field_local_dim_le_two
      Q.primeCompl φ p q hregular hpmax hq (hdim Q)
  let f : S →+* Localization.AtPrime P := localizationQuotientAtPrimeMap I P
  have hfp : f (algebraMap A S p) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI, map_zero]
  have hfq : f (algebraMap A S q) = 0 := by
    dsimp [f, localizationQuotientAtPrimeMap]
    rw [IsLocalization.lift_eq]
    change (algebraMap (A ⧸ I) (Localization.AtPrime P)) (Ideal.Quotient.mk I q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI, map_zero]
  have hJ : J ≤ RingHom.ker f := by
    apply sup_le
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S p)
      exact hfp
    · rw [Ideal.span_le]
      rintro x (rfl : x = algebraMap A S q)
      exact hfq
  let fbar : S ⧸ J →+* Localization.AtPrime P :=
    Ideal.Quotient.lift J f (fun x hx => show f x = 0 from hJ hx)
  have hfbar : Function.Surjective fbar := by
    intro x
    obtain ⟨y, hy⟩ := localizationQuotientAtPrimeMap_surjective I P x
    refine ⟨Ideal.Quotient.mk J y, ?_⟩
    dsimp [fbar]
    change f y = x
    exact hy
  letI : IsArtinianRing (S ⧸ J) := hArt
  exact isArtinianRing_of_surjective fbar hfbar

/-- The affine-surface calculation applied to one residue-field fibre.  Unlike
the older local-chart form, this needs dimension two only after localizing at
the maximal ideals of the whole fibre ring. -/
theorem isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    [IsNoetherianRing (P.asIdeal.Fiber S)]
    (hregular : IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) = 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) := by
  exact
    isArtinianRing_quotient_pair_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_two
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b) hregular hdim

/-- For a finite-type affine family, its residue-field fibres are noetherian
automatically.  Thus the fibrewise regular-pair surface calculation needs no
separate noetherianity datum. -/
theorem isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) = 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) := by
  letI : IsNoetherianRing (P.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing P.asIdeal.ResidueField (P.asIdeal.Fiber S)
  exact
    isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_two
      P a b hregular hdim

/-- Fibrewise regularity on an affine family itself supplies the residue-fibre
regularity required by the Artinian surface calculation. -/
theorem isArtinianRing_quotient_pair_fiber_of_base_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair (algebraMap R S) a b)
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) = 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) :=
  isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_two
    P a b (hregular.fiber P a b) hdim

/-- The residue-field fibre form of the affine surface calculation with local
Krull dimension bounded by two. -/
theorem isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_le_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    [IsNoetherianRing (P.asIdeal.Fiber S)]
    (hregular : IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) := by
  exact
    isArtinianRing_quotient_pair_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_le_two
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b) hregular hdim

/-- Finite type supplies noetherianity for the local-dimension-at-most-two
residue-fibre calculation. -/
theorem isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_le_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) := by
  letI : IsNoetherianRing (P.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing P.asIdeal.ResidueField (P.asIdeal.Fiber S)
  exact
    isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_le_two
      P a b hregular hdim

/-- Base-fibrewise regularity transports to the residue fibre before applying
the local-dimension-at-most-two calculation. -/
theorem isArtinianRing_quotient_pair_fiber_of_base_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_le_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (P : PrimeSpectrum R) (a b : S)
    (hregular : IsFibrewiseRegularPair (algebraMap R S) a b)
    (hdim : ∀ (Q : Ideal (P.asIdeal.Fiber S)) [Q.IsMaximal],
      ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) :=
  isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_le_two
    P a b (hregular.fiber P a b) hdim

/-- The preceding local-to-global criterion gives the dimension-zero form
needed for an affine fibre of the pencil. -/
theorem topologicalKrullDim_primeSpectrum_le_zero_of_isArtinianRing_at_maximal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Rₚ : ∀ P : Ideal R, [P.IsMaximal] → Type*)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsArtinianRing (Rₚ P)) :
    topologicalKrullDim (PrimeSpectrum R) ≤ 0 := by
  have hArt : IsArtinianRing R :=
    isArtinianRing_of_isArtinianRing_at_maximal Rₚ h
  have hdim : Ring.KrullDimLE 0 R :=
    isArtinianRing_iff_krullDimLE_zero.mp hArt
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim,
    Nat.cast_zero] at hdim
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hdim

/-- The scheme-level affine form of the local-to-global dimension-zero
criterion. -/
theorem topologicalKrullDim_spec_le_zero_of_isArtinianRing_at_maximal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Rₚ : ∀ P : Ideal R, [P.IsMaximal] → Type*)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsArtinianRing (Rₚ P)) :
    topologicalKrullDim (AlgebraicGeometry.Spec (.of R)) ≤ 0 := by
  change topologicalKrullDim (PrimeSpectrum R) ≤ 0
  exact topologicalKrullDim_primeSpectrum_le_zero_of_isArtinianRing_at_maximal Rₚ h

/-- The affine scheme determined by a noetherian ring is Artinian when its
maximal localizations are Artinian. This is the form used after identifying a
local pencil fibre with an affine coordinate quotient. -/
theorem isArtinianScheme_spec_of_isArtinianRing_at_maximal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Rₚ : ∀ P : Ideal R, [P.IsMaximal] → Type*)
    [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsArtinianRing (Rₚ P)) :
    AlgebraicGeometry.IsArtinianScheme (AlgebraicGeometry.Spec (.of R)) := by
  let : IsArtinianRing R := isArtinianRing_of_isArtinianRing_at_maximal Rₚ h
  infer_instance

universe u

/-- Base change to a residue field commutes with an affine quotient.  The
right-hand side is the quotient of the residue-field fibre ring by the
extension of the original ideal. -/
noncomputable def fiberQuotientAlgEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (I : Ideal S) :
    p.asIdeal.Fiber (S ⧸ I) ≃ₐ[p.asIdeal.ResidueField]
      ((p.asIdeal.Fiber S) ⧸ I.map
        (Algebra.TensorProduct.includeRight (A := p.asIdeal.ResidueField) (R := R))) :=
  Algebra.TensorProduct.tensorQuotientEquiv
    (R := R) p.asIdeal.ResidueField S p.asIdeal.ResidueField I

/-- The preceding equivalence for the ideal generated by two elements.  It
identifies the fibre of a two-coordinate zero locus with the quotient by the
two induced residue-field coordinates. -/
noncomputable def fiberQuotientPairAlgEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (a b : S) :
    p.asIdeal.Fiber (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b})) ≃ₐ[p.asIdeal.ResidueField]
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)))) := by
  let e := fiberQuotientAlgEquiv p (Ideal.span {a} ⊔ Ideal.span {b})
  apply e.trans
  apply Ideal.quotientEquivAlgOfEq p.asIdeal.ResidueField
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  simp

/-- A residue-field fibre of an affine quotient is Artinian as soon as the
corresponding quotient of the residue-field fibre ring is Artinian.  The
tensor--quotient equivalence identifies these two coordinate rings, while
`Spec.fiberToSpecResidueFieldIso` identifies the resulting affine scheme with
the actual scheme-theoretic fibre. -/
theorem isArtinianScheme_fiber_spec_quotient_of_isArtinianRing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (I : Ideal S)
    [IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸ I.map
        (Algebra.TensorProduct.includeRight (A := p.asIdeal.ResidueField) (R := R)))] :
    AlgebraicGeometry.IsArtinianScheme
      ((AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (S ⧸ I)))).fiber p) := by
  let e := fiberQuotientAlgEquiv p I
  let : IsArtinianRing (p.asIdeal.Fiber (S ⧸ I)) :=
    e.symm.toRingEquiv.isArtinianRing
  let E := AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso R (S ⧸ I) p
  let hArt : AlgebraicGeometry.IsArtinianScheme
      (AlgebraicGeometry.Spec (.of (p.asIdeal.Fiber (S ⧸ I)))) := by
    infer_instance
  let : AlgebraicGeometry.IsLocallyArtinian
      ((AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (S ⧸ I)))).fiber p) :=
    @AlgebraicGeometry.IsLocallyArtinian.of_isImmersion _
      (AlgebraicGeometry.Spec (.of (p.asIdeal.Fiber (S ⧸ I)))) E.hom.left _
      hArt.toIsLocallyArtinian
  let : CompactSpace
      ((AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (S ⧸ I)))).fiber p) :=
    @AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace _
      (AlgebraicGeometry.Spec (.of (p.asIdeal.Fiber (S ⧸ I)))) E.hom.left _
      hArt.toCompactSpace
  exact ⟨⟩

/-- For a two-coordinate affine zero locus, the quotient of the
residue-field fibre is precisely the quotient by the two induced
coordinates.  This is the coordinate-ring form needed for a normalized
rank-two pencil. -/
theorem isArtinianScheme_fiber_spec_quotient_pair_of_isArtinianRing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (a b : S)
    [IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))] :
    AlgebraicGeometry.IsArtinianScheme
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))))).fiber p) := by
  have hI :
      (Ideal.span ({a} : Set S) ⊔ Ideal.span {b}).map
        (Algebra.TensorProduct.includeRight (A := p.asIdeal.ResidueField) (R := R)) =
        Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span]
    simp
  let : IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸ (Ideal.span ({a} : Set S) ⊔ Ideal.span {b}).map
        (Algebra.TensorProduct.includeRight (A := p.asIdeal.ResidueField) (R := R))) := by
    rw [hI]
    infer_instance
  exact isArtinianScheme_fiber_spec_quotient_of_isArtinianRing p
    (Ideal.span {a} ⊔ Ideal.span {b})

/-- On a two-dimensional local residue-field fibre, two successive
non-zero-divisors cut the actual affine two-coordinate scheme fibre down to
an Artinian scheme.  This joins the local regular-sequence calculation to the
scheme-theoretic fibre of the corresponding affine zero locus. -/
theorem isArtinianScheme_fiber_spec_quotient_pair_of_local_dim_two_nonZeroDivisors
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    [IsNoetherianRing (P.asIdeal.Fiber S)] [IsLocalRing (P.asIdeal.Fiber S)]
    (ha : (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) ∈ (P.asIdeal.Fiber S)⁰)
    (hamax : (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) ∈
      IsLocalRing.maximalIdeal (P.asIdeal.Fiber S))
    (hbreg : Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})
        (1 ⊗ₜ[R] b) ∈
      ((P.asIdeal.Fiber S) ⧸ Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})⁰)
    (hb : Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})
        (1 ⊗ₜ[R] b) ∈
      (IsLocalRing.maximalIdeal (P.asIdeal.Fiber S)).map
        (Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})))
    (hdim : ringKrullDim (P.asIdeal.Fiber S) = 2) :
    AlgebraicGeometry.IsArtinianScheme
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))))).fiber P) := by
  let : IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) :=
    isArtinianRing_quotient_pair_of_local_dim_two_nonZeroDivisors
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b) ha hamax hbreg hb hdim
  exact isArtinianScheme_fiber_spec_quotient_pair_of_isArtinianRing P a b

/-- On a two-dimensional local residue-field fibre, the fibrewise-regular
form of a pair of coordinates cuts the associated affine two-coordinate
scheme fibre down to an Artinian scheme.  This is the version used by the
Serre-pencil charts: regularity is supplied over the residue field, while the
two membership hypotheses record that the chosen local point is a common
zero of the coordinates. -/
theorem isArtinianScheme_fiber_spec_quotient_pair_of_fibrewiseRegularPair_local_dim_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : PrimeSpectrum R) (a b : S)
    [IsNoetherianRing (P.asIdeal.Fiber S)] [IsLocalRing (P.asIdeal.Fiber S)]
    (hregular : IsFibrewiseRegularPair
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hamax : (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) ∈
      IsLocalRing.maximalIdeal (P.asIdeal.Fiber S))
    (hb : Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})
        (1 ⊗ₜ[R] b) ∈
      (IsLocalRing.maximalIdeal (P.asIdeal.Fiber S)).map
        (Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)})))
    (hdim : ringKrullDim (P.asIdeal.Fiber S) = 2) :
    AlgebraicGeometry.IsArtinianScheme
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))))).fiber P) := by
  let : IsArtinianRing
      ((P.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : P.asIdeal.Fiber S)} : Set (P.asIdeal.Fiber S)))) :=
    isArtinianRing_quotient_pair_of_fibrewiseRegularPair_over_field
      (algebraMap P.asIdeal.ResidueField (P.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : P.asIdeal.Fiber S) (1 ⊗ₜ[R] b) hregular hamax hb hdim
  exact isArtinianScheme_fiber_spec_quotient_pair_of_isArtinianRing P a b

/-- A locally finite-type scheme morphism with Artinian scheme-theoretic
fibres is locally quasi-finite.  This turns the affine residue-field fibre
calculation into the morphism property consumed by the Serre-pencil gluing
argument. -/
theorem locallyQuasiFinite_of_artinianScheme_fibers
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyOfFiniteType f]
    (h : ∀ y : Y, AlgebraicGeometry.IsArtinianScheme (f.fiber y)) :
    AlgebraicGeometry.LocallyQuasiFinite f := by
  apply AlgebraicGeometry.LocallyQuasiFinite.of_fiberToSpecResidueField
  intro y
  letI : AlgebraicGeometry.IsArtinianScheme (f.fiber y) := h y
  letI : AlgebraicGeometry.LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    change AlgebraicGeometry.LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  letI : AlgebraicGeometry.LocallyQuasiFinite (f.fiberToSpecResidueField y) :=
    AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton _
      (fun _ ↦ Set.toFinite _)
  letI : AlgebraicGeometry.IsFinite (f.fiberToSpecResidueField y) :=
    AlgebraicGeometry.IsFinite.of_locallyQuasiFinite _
  infer_instance

/-- Local quasi-finiteness transfers across an isomorphism of source and
target that conjugates two scheme morphisms. -/
theorem locallyQuasiFinite_of_iso_square
    {X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    [AlgebraicGeometry.LocallyQuasiFinite f']
    (h : eX.hom ≫ f' = f ≫ eY.hom) :
    AlgebraicGeometry.LocallyQuasiFinite f := by
  have hf : f = eX.hom ≫ f' ≫ eY.inv := by
    rw [← Category.assoc, h, Category.assoc, eY.hom_inv_id, Category.comp_id]
  rw [hf]
  infer_instance

/-- A two-coordinate affine quotient is locally quasi-finite once its
residue-field coordinate quotients are Artinian and the quotient morphism is
locally of finite type. -/
theorem locallyQuasiFinite_spec_quotient_pair_of_isArtinianRing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S)
    [AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b})))))]
    (h : ∀ p : PrimeSpectrum R,
      IsArtinianRing
        ((p.asIdeal.Fiber S) ⧸
          (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
            Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))) :
    AlgebraicGeometry.LocallyQuasiFinite
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))))) := by
  apply locallyQuasiFinite_of_artinianScheme_fibers
  intro p
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)))) := h p
  exact isArtinianScheme_fiber_spec_quotient_pair_of_isArtinianRing p a b

/-- A two-coordinate affine quotient is locally quasi-finite when every
residue-field fibre is a two-dimensional local chart on which the coordinates
form a fibrewise regular pair and vanish at its closed point.  This packages
the regular-pair dimension calculation directly as the quasi-finiteness
criterion used by the normalized Serre-pencil charts. -/
theorem locallyQuasiFinite_spec_quotient_pair_of_fibrewiseRegularPair_local_dim_two
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S)
    [AlgebraicGeometry.LocallyOfFiniteType
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b})))))]
    (hnoetherian : ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S))
    (hlocal : ∀ p : PrimeSpectrum R, IsLocalRing (p.asIdeal.Fiber S))
    (hregular : ∀ p : PrimeSpectrum R, IsFibrewiseRegularPair
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
      (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hamax : ∀ p : PrimeSpectrum R, (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) ∈
      IsLocalRing.maximalIdeal (p.asIdeal.Fiber S))
    (hb : ∀ p : PrimeSpectrum R,
      Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)})
        (1 ⊗ₜ[R] b) ∈
      (IsLocalRing.maximalIdeal (p.asIdeal.Fiber S)).map
        (Ideal.Quotient.mk (Ideal.span {(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)})))
    (hdim : ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber S) = 2) :
    AlgebraicGeometry.LocallyQuasiFinite
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (S ⧸ (Ideal.span {a} ⊔ Ideal.span {b}))))) := by
  apply locallyQuasiFinite_of_artinianScheme_fibers
  intro p
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : IsNoetherianRing (p.asIdeal.Fiber S) := hnoetherian p
  letI : IsLocalRing (p.asIdeal.Fiber S) := hlocal p
  exact isArtinianScheme_fiber_spec_quotient_pair_of_fibrewiseRegularPair_local_dim_two
    p a b (hregular p) (hamax p) (hb p) (hdim p)

end AllCharacteristics
