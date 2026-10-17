import PfaffianDescent.VoisinRegularLocalDepth
import AllCharacteristics.RegularParameters
import Mathlib.RingTheory.Artinian.Ring

/-! # A finite two-coordinate zero on a regular surface is a regular pair -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_prime_eq_maximal_of_artinian_pair
    {R : Type u} [CommRing R] [IsLocalRing R] (a b : R)
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))]
    (P : Ideal R) [P.IsPrime] (ha : a ∈ P) (hb : b ∈ P) : P = maximalIdeal R := by
  let I := Ideal.span ({a, b} : Set R)
  have hI : I ≤ P := Ideal.span_le.mpr (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha
    · exact Set.mem_singleton_iff.mp hx ▸ hb)
  let f := Ideal.Quotient.mk I
  have hk : RingHom.ker f ≤ P := by simpa only [f, Ideal.mk_ker] using hI
  letI : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hk
  letI : (P.map f).IsMaximal := inferInstance
  have hm : (P.map f).comap f = P := by
    rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hk]
  have hP : P.IsMaximal := hm ▸ Ideal.comap_isMaximal_of_surjective f Ideal.Quotient.mk_surjective
  exact (IsLocalRing.isMaximal_iff (I := P)).mp hP

theorem cubicClosedPointSerreFiniteZeroResidual_regular_pair_of_artinian_quotient
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 2) (a b : R)
    (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R)
    [IsArtinianRing (R ⧸ Ideal.span ({a, b} : Set R))] : IsRegular R [a, b] := by
  have ha₀ : a ≠ 0 := by
    intro hzero
    have hI : Ideal.span ({a, b} : Set R) = Ideal.span {b} := by simp [hzero]
    letI : IsArtinianRing (R ⧸ Ideal.span {b}) := hI ▸ inferInstance
    have hdim := AllCharacteristics.ringKrullDim_le_parameter_quotient_add_one b hb
    have hz : ringKrullDim (R ⧸ Ideal.span {b}) ≤ 0 := Ring.krullDimLE_iff.mp inferInstance
    have hdim' := hdim.trans (by simpa only [add_comm] using add_le_add_right hz 1)
    rw [hd] at hdim'
    norm_num at hdim' 
  letI := AllCharacteristics.isDomain_of_regularLocalRing R
  have har : IsSMulRegular R a :=
    (isSMulRegular_iff_right_eq_zero_of_smul).mpr
      (fun x hx => (mul_eq_zero.mp hx).resolve_left ha₀)
  have hreg : IsWeaklyRegular R [a] := (isWeaklyRegular_singleton_iff R a).mpr har
  have hn : maximalIdeal R ∉ associatedPrimes R (R ⧸ Ideal.span {a}) := by
    have hspan : (maximalIdeal R).spanFinrank = 2 := by
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
      rw [hd] at h
      exact_mod_cast h
    have hn₀ := regularLocal_maximalIdeal_not_associated_quotient_ofList R [a] hreg
      (by simp [hspan])
    exact (Ideal.ofList_singleton a) ▸ hn₀
  have hbr : IsSMulRegular (R ⧸ Ideal.span {a}) b := by
    by_contra H
    have H' : b ∈ ⋃ P ∈ associatedPrimes R (R ⧸ Ideal.span {a}), (P : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact H
    simp only [Set.mem_iUnion] at H'
    obtain ⟨P, hP, hbP⟩ := H'
    letI : P.IsPrime := hP.1
    have haP : a ∈ P := by
      have hle := hP.annihilator_le
      rw [show (⊤ : Submodule R (R ⧸ Ideal.span {a})).annihilator =
        Ideal.span {a} from Submodule.annihilator_top.trans Ideal.annihilator_quotient] at hle
      exact hle (Ideal.subset_span (by simp))
    have he := cubicClosedPointSerreFiniteZeroResidual_prime_eq_maximal_of_artinian_pair a b P haP hbP
    exact hn (he ▸ hP)
  have heq : a • (⊤ : Submodule R R) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop a R ≃ₗ[R] R ⧸ Ideal.span {a} := Submodule.quotEquivOfEq _ _ heq
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R (by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact List.mem_singleton.mp hx ▸ hb)
  apply ((isWeaklyRegular_singleton_iff (QuotSMulTop a R) b).mpr
    ((e.isSMulRegular_congr b).mpr hbr)).cons
  exact har

end PfaffianDescent
