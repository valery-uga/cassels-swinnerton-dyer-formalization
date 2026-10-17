import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import PfaffianDescent.TwoGeneratorKoszul
import Mathlib.Tactic.Abel

/-! Algebraic cuts for the
actual prescribed-ideal regularity lift. No regular pair is assumed upstairs. -/
noncomputable section
namespace PfaffianDescent
open LinearMap TensorProduct
open scoped nonZeroDivisors
universe u v w

/-- The kernel of a surjection between flat modules is flat. This is used
with A -> A/J, deriving J-flatness rather than assuming it. -/
lemma flat_kernel_of_surjective_flat167
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Flat R f.ker := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ t ht
  let k : f.ker →ₗ[R] M := f.ker.subtype
  have hkX : Function.Injective (k.lTensor X) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf k
      f.ker.subtype_injective (LinearMap.exact_subtype_ker_map f) X
  have hM : Function.Injective (t.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap t ht
  have hcomm : (k.lTensor Y).comp (t.rTensor f.ker) =
      (t.rTensor M).comp (k.lTensor X) := by
    ext x y
    simp
  intro x y hxy
  apply hkX
  apply hM
  change ((t.rTensor M).comp (k.lTensor X)) x =
    ((t.rTensor M).comp (k.lTensor X)) y
  rw [← hcomm]
  exact congrArg (k.lTensor Y) hxy

/-- Nilpotent relative Nakayama without finiteness: an error in I*P can
be iterated until it vanishes. Used for K <= image(delta2) + I*K. -/
lemma submodule_le_of_nilpotent_smul_error167
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (P Q : Submodule R M)
    (h : P ≤ Q ⊔ I • P) : P ≤ Q := by
  have hpow (n : ℕ) : P ≤ Q ⊔ (I ^ n) • P := by
    induction n with
    | zero => simpa only [pow_zero, one_smul]
        using (le_sup_right : P ≤ Q ⊔ P)
    | succ n ih =>
      have hstep : (I ^ n) • P ≤ (I ^ n) • Q ⊔ (I ^ (n + 1)) • P := by
        have hh := smul_mono_right (I ^ n) h
        simpa only [Submodule.smul_sup, ← Submodule.mul_smul, pow_succ] using hh
      calc
        P ≤ Q ⊔ (I ^ n) • P := ih
        _ ≤ Q ⊔ ((I ^ n) • Q ⊔ (I ^ (n + 1)) • P) := sup_le_sup_left hstep Q
        _ = (Q ⊔ (I ^ n) • Q) ⊔ (I ^ (n + 1)) • P := by simp only [sup_assoc]
        _ = Q ⊔ (I ^ (n + 1)) • P := by
          rw [sup_eq_left.mpr (show (I ^ n) • Q ≤ Q from Submodule.smul_le_right)]
  obtain ⟨n, hn⟩ := hI
  simpa only [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] using hpow n

/-- Derive flatness of the prescribed whole ideal from ambient flatness and
its actual quotient flatness. No flatness of a principal quotient is supplied. -/
lemma flat_prescribedIdeal_of_ambient_and_quotient_flat167
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (J : Ideal A) [Module.Flat R A] [Module.Flat R (A ⧸ J)] :
    Module.Flat R (J.restrictScalars R) := by
  let JR := J.restrictScalars R
  letI : Module.Flat R (A ⧸ JR) :=
    Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R J)
  have h := flat_kernel_of_surjective_flat167 JR.mkQ JR.mkQ_surjective
  rw [Submodule.ker_mkQ] at h
  exact h

/-- Two-generator syzygies lift across a nilpotent base thickening, for
ANY actual flat ambient algebra and prescribed flat quotient. The whole-ideal
generation hypothesis is supplied by the independent generation167 theorem. -/
lemma twoGenerator_exact_of_nilpotent_reduction167
    {R : Type u} {A : Type v} {A0 : Type w} [CommRing R] [CommRing A] [CommRing A0] [Algebra R A]
    [Module.Flat R A]
    (π : A →+* A0) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)]
    (f g : A) (hspan : J = Ideal.span ({f, g} : Set A))
    (hf0 : π f ∈ A0⁰)
    (hg0 : Ideal.Quotient.mk (Ideal.span {π f}) (π g) ∈
      (A0 ⧸ Ideal.span {π f})⁰) :
    LinearMap.range (twoGeneratorFirst f g) =
      LinearMap.ker (twoGeneratorLast f g) := by
  let JR := J.restrictScalars R
  letI : Module.Flat R JR :=
    flat_prescribedIdeal_of_ambient_and_quotient_flat167 J
  let d1 : (A × A) →ₗ[R] JR :=
    ((twoGeneratorLast f g).restrictScalars R).codRestrict JR (fun v => by
      change twoGeneratorLast f g v ∈ J
      rw [hspan, ← twoGeneratorLast_range]
      exact LinearMap.mem_range_self (twoGeneratorLast f g) v)
  have hd1 : Function.Surjective d1 := by
    intro y
    have hy : (y : A) ∈ LinearMap.range (twoGeneratorLast f g) := by
      rw [twoGeneratorLast_range, ← hspan]
      exact y.property
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Subtype.ext hv⟩
  let d2 : A →ₗ[R] A × A := (twoGeneratorFirst f g).restrictScalars R
  let K := d1.ker
  have hLK : d2.range ≤ K := by
    rintro v ⟨c, rfl⟩
    change d1 (d2 c) = 0
    apply Subtype.ext
    exact LinearMap.congr_fun (twoGenerator_comp_zero f g) c
  have hinter : K ⊓ I • (⊤ : Submodule R (A × A)) = I • K :=
    LinearMap.ker_inf_smul_top_eq_smul_of_flat I d1 hd1
  have herror : K ≤ d2.range ⊔ I • K := by
    intro v hv
    have hv0 : (π v.1, π v.2) ∈ LinearMap.ker (twoGeneratorLast (π f) (π g)) := by
      have hvA : f * v.1 + g * v.2 = 0 :=
        congrArg Subtype.val (show d1 v = 0 from hv)
      change π f * π v.1 + π g * π v.2 = 0
      simpa only [map_add, map_mul, map_zero] using congrArg π hvA
    rw [← twoGenerator_exact_of_regular hf0 hg0] at hv0
    obtain ⟨c0, hc0⟩ := hv0
    obtain ⟨c, hc⟩ := hπ c0
    have hc1 : -(π g) * c0 = π v.1 := congrArg Prod.fst hc0
    have hc2 : π f * c0 = π v.2 := congrArg Prod.snd hc0
    let w := v - d2 c
    have hwK : w ∈ K := K.sub_mem hv (hLK (LinearMap.mem_range_self d2 c))
    have hw1 : π w.1 = 0 := by
      change π (v.1 - (-g * c)) = 0
      rw [map_sub, map_mul, map_neg, hc, hc1, sub_self]
    have hw2 : π w.2 = 0 := by
      change π (v.2 - f * c) = 0
      rw [map_sub, map_mul, hc, hc2, sub_self]
    have hcoord {a : A} (ha : π a = 0) : a ∈ I • (⊤ : Submodule R A) := by
      rw [Ideal.smul_top_eq_map, ← hker]
      exact ha
    have hleft : (w.1, 0) ∈ I • (⊤ : Submodule R (A × A)) := by
      have hm : (w.1, 0) ∈ (I • (⊤ : Submodule R A)).map
          (LinearMap.inl R A A) :=
        Submodule.mem_map.mpr ⟨w.1, hcoord hw1, rfl⟩
      rw [Submodule.map_smul''] at hm
      exact (show I • (⊤ : Submodule R A).map (LinearMap.inl R A A) ≤
        I • (⊤ : Submodule R (A × A)) from smul_mono_right I le_top) hm
    have hright : (0, w.2) ∈ I • (⊤ : Submodule R (A × A)) := by
      have hm : (0, w.2) ∈ (I • (⊤ : Submodule R A)).map
          (LinearMap.inr R A A) :=
        Submodule.mem_map.mpr ⟨w.2, hcoord hw2, rfl⟩
      rw [Submodule.map_smul''] at hm
      exact (show I • (⊤ : Submodule R A).map (LinearMap.inr R A A) ≤
        I • (⊤ : Submodule R (A × A)) from smul_mono_right I le_top) hm
    have hwI : w ∈ I • (⊤ : Submodule R (A × A)) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using
        Submodule.add_mem _ hleft hright
    have hw : w ∈ I • K := by
      rw [← hinter]
      exact ⟨hwK, hwI⟩
    have hsum : d2 c + w = v := by dsimp only [w]; abel
    rw [← hsum]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self d2 c) hw
  have hKL : K ≤ d2.range :=
    submodule_le_of_nilpotent_smul_error167 I hI K d2.range herror
  have hEq : d2.range = K := le_antisymm hLK hKL
  ext v
  change v ∈ d2.range ↔ twoGeneratorLast f g v = 0
  rw [hEq]
  change d1 v = 0 ↔ twoGeneratorLast f g v = 0
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

private def multiplicationLinear167
    {A : Type v} [CommRing A] (f : A) : A →ₗ[A] A where
  toFun x := f * x
  map_add' x y := mul_add f x y
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- At the actual local Noetherian stalk, lifted Koszul H1 exactness
implies both required non-zero-divisor assertions. The first uses ann(f)
Nakayama; the second is read directly from the syzygies. -/
lemma regularPair_of_localNoetherian_syzygy_exact167
    {A : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f g : A) (hg : g ∈ IsLocalRing.maximalIdeal A)
    (hexact : LinearMap.range (twoGeneratorFirst f g) =
      LinearMap.ker (twoGeneratorLast f g)) :
    f ∈ A⁰ ∧ Ideal.Quotient.mk (Ideal.span {f}) g ∈ (A ⧸ Ideal.span {f})⁰ := by
  let N : Submodule A A := (multiplicationLinear167 f).ker
  have hN : N ≤ (Ideal.span {g}) • N := by
    intro a ha
    have hfa : f * a = 0 := ha
    have hsyz : (a, 0) ∈ LinearMap.ker (twoGeneratorLast f g) := by
      change f * a + g * 0 = 0
      simpa using hfa
    rw [← hexact] at hsyz
    obtain ⟨b, hb⟩ := hsyz
    have hb1 : -g * b = a := congrArg Prod.fst hb
    have hb2 : f * b = 0 := congrArg Prod.snd hb
    have hbN : b ∈ N := hb2
    have hgb : g * b ∈ (Ideal.span {g}) • N :=
      Submodule.smul_mem_smul (Ideal.subset_span (by simp)) hbN
    rw [← hb1, neg_mul]
    exact Submodule.neg_mem _ hgb
  have hgj : Ideal.span {g} ≤ Ideal.jacobson (⊥ : Ideal A) :=
    (Ideal.span_le.mpr (by
      intro x hx
      have hxg : x = g := Set.mem_singleton_iff.mp hx
      exact hxg ▸ hg)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hzero : N = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {g}) N
      (IsNoetherian.noetherian N) hN hgj
  have hf : f ∈ A⁰ := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro a ha
    have hmem : a ∈ N := ha
    rw [hzero] at hmem
    exact (Submodule.mem_bot A).mp hmem
  refine ⟨hf, ?_⟩
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hga : g * a ∈ Ideal.span {f} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hga
  have hsyz : (b, -a) ∈ LinearMap.ker (twoGeneratorLast f g) := by
    change f * b + g * -a = 0
    linear_combination hb
  rw [← hexact] at hsyz
  obtain ⟨c, hc⟩ := hsyz
  have hc2 : f * c = -a := congrArg Prod.snd hc
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨-c, ?_⟩
  linear_combination -hc2

/-- Genuine upstairs regularity from flat ambient + prescribed flat quotient,
actual nilpotent reduction, downstairs pair regularity and generated ideal.
No upstairs regularity, principal quotient flatness or pair certificate input. -/
lemma regularPair_of_nilpotent_reduction_flat_quotient167
    {R : Type u} {A : Type v} {A0 : Type w} [CommRing R] [CommRing A] [CommRing A0] [Algebra R A]
    [Module.Flat R A] [IsLocalRing A] [IsNoetherianRing A]
    (π : A →+* A0) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)]
    (f g : A) (hspan : J = Ideal.span ({f, g} : Set A))
    (hJ : J ≠ ⊤)
    (hf0 : π f ∈ A0⁰)
    (hg0 : Ideal.Quotient.mk (Ideal.span {π f}) (π g) ∈
      (A0 ⧸ Ideal.span {π f})⁰) :
    f ∈ A⁰ ∧ Ideal.Quotient.mk (Ideal.span {f}) g ∈ (A ⧸ Ideal.span {f})⁰ := by
  have hgJ : g ∈ J := by
    rw [hspan]
    exact Ideal.subset_span (by simp)
  exact regularPair_of_localNoetherian_syzygy_exact167 f g
    (IsLocalRing.le_maximalIdeal hJ hgJ)
    (twoGenerator_exact_of_nilpotent_reduction167 π hπ I hI hker J f g hspan hf0 hg0)

end PfaffianDescent

