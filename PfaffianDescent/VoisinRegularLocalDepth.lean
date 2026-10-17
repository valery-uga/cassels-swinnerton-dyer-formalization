import AllCharacteristics.RegularLocalDomain
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.Regular
import PfaffianDescent.ExtMapFixedSource

/-!
# Depth of regular local rings for Voisin's complete intersections

The cubic--quadric unmixedness argument needs depth, not just regularity of
the two equations. We construct regular sequences of every length up to the
dimension of a regular local ring, using successive minimal parameters.
The construction uses the proved domain and parameter-quotient results from
`AllCharacteristics`; Cohen--Macaulayness is not an additional assumption.
-/

namespace PfaffianDescent

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

universe u

/-- A regular local ring has a regular sequence in its maximal ideal of any
length at most its dimension, expressed as the number of minimal generators. -/
theorem exists_isRegular_of_le_regularLocal_spanFinrank (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      n ≤ (maximalIdeal R).spanFinrank →
      ∃ rs : List R, rs.length = n ∧
        (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular R rs := by
  classical
  induction n with
  | zero =>
    intro R _ _ _
    exact ⟨[], rfl, by simp, IsRegular.nil R R⟩
  | succ n ih =>
    intro R _ _ hn
    have hd : ringKrullDim R ≠ 0 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
      exact_mod_cast (show (maximalIdeal R).spanFinrank ≠ 0 by omega)
    obtain ⟨x, hx, hx₂, _⟩ :=
      AllCharacteristics.exists_parameter_avoiding_minimal_primes hd
    have hx₀ : x ≠ 0 := fun h => hx₂ (h ▸ Ideal.zero_mem _)
    let := AllCharacteristics.isDomain_of_regularLocalRing R
    let := AllCharacteristics.isRegularLocalRing_quotient_parameter x hx hx₂
    have hdim : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by
      have h := AllCharacteristics.ringKrullDim_quotient_parameter_add_one x hx hx₂
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R),
        ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ Ideal.span {x})] at h
      exact_mod_cast h
    obtain ⟨qs, hlen, hmem, hreg⟩ := ih (R ⧸ Ideal.span {x}) (by omega)
    let lift : (R ⧸ Ideal.span {x}) → R :=
      fun a => Classical.choose (Ideal.Quotient.mk_surjective a)
    have hlift : ∀ a, Ideal.Quotient.mk (Ideal.span {x}) (lift a) = a :=
      fun a => Classical.choose_spec (Ideal.Quotient.mk_surjective a)
    let rs := qs.map lift
    have hrs : rs.map (Ideal.Quotient.mk (Ideal.span {x})) = qs := by
      simp [rs, List.map_map, Function.comp_def, hlift]
    have hrs_mem : ∀ r ∈ rs, r ∈ maximalIdeal R := by
      intro r hr
      have hqr := hmem (Ideal.Quotient.mk (Ideal.span {x}) r)
        (hrs ▸ List.mem_map_of_mem hr)
      exact fun hu => hqr (hu.map (Ideal.Quotient.mk (Ideal.span {x})))
    have heq : x • (⊤ : Submodule R R) = Ideal.span {x} := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
      Submodule.quotEquivOfEq _ _ heq
    have hweak : IsWeaklyRegular (QuotSMulTop x R) rs := by
      apply (e.isWeaklyRegular_congr rs).mpr
      apply (isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}) _ rs).mp
      simpa only [Ideal.Quotient.algebraMap_eq, hrs] using hreg.toIsWeaklyRegular
    refine ⟨x :: rs, ?_, ?_, ?_⟩
    · have := congrArg List.length hrs
      simpa only [List.length_cons, List.length_map, hlen] using congrArg Nat.succ this
    · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hx hrs_mem
    · apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R
        (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hx hrs_mem)
      apply hweak.cons
      exact (isSMulRegular_iff_right_eq_zero_of_smul).mpr
        (fun y hy => (mul_eq_zero.mp hy).resolve_left hx₀)

open CategoryTheory CategoryTheory.Abelian

/-- The residue field has no Ext into a regular local ring below the dimension.
This is the depth assertion used to exclude embedded components. -/
theorem regularLocal_residue_ext_subsingleton
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (i : ℕ) (hi : i < (maximalIdeal R).spanFinrank) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    exists_isRegular_of_le_regularLocal_spanFinrank (maximalIdeal R).spanFinrank R le_rfl
  apply ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R)
    (ModuleCat.of R (R ⧸ maximalIdeal R)) _ (ModuleCat.of R R) _ rs hmem hreg i
    (by omega)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · change maximalIdeal R • (⊤ : Ideal R) < ⊤
    simpa only [smul_eq_mul, Ideal.mul_top] using (maximalIdeal.isMaximal R).lt_top

/-- Killing a regular element lowers an Ext-vanishing range by at most one. -/
theorem ext_quotSMulTop_subsingleton_of_isSMulRegular
    {R : Type u} [CommRing R] (N M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (i : ℕ)
    (h₀ : Subsingleton (Ext N M i)) (h₁ : Subsingleton (Ext N M (i + 1))) :
    Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) := by
  have zero₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₀
  have zero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₁
  exact AddCommGrpCat.subsingleton_of_isZero <| CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros
    ((Ext.covariant_sequence_exact₃' N hx.smulShortComplex_shortExact) i (i + 1) rfl)
    (zero₀.eq_zero_of_src _) (zero₁.eq_zero_of_tgt _)

/-- Quotienting by a weakly regular sequence lowers an Ext-vanishing range
by at most the length of that sequence. -/
theorem ext_quotient_ofList_subsingleton_of_isWeaklyRegular
    {R : Type u} [CommRing R] (N M : ModuleCat.{u} R)
    (rs : List R) (hreg : IsWeaklyRegular M rs) (i : ℕ)
    (hExt : ∀ j, i ≤ j → j ≤ i + rs.length → Subsingleton (Ext N M j)) :
    Subsingleton (Ext N
      (ModuleCat.of R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) i) := by
  induction rs generalizing M with
  | nil =>
    have := hExt i le_rfl (by simp)
    let e := Submodule.quotEquivOfEqBot
      (Ideal.ofList ([] : List R) • (⊤ : Submodule R M)) (by simp)
    exact ext_subsingleton_of_iso_right e.symm.toModuleIso i
  | cons x rs ih =>
    obtain ⟨hx, htail⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg
    have hquot : ∀ j, i ≤ j → j ≤ i + rs.length →
        Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) j) := by
      intro j hj₀ hj₁
      apply ext_quotSMulTop_subsingleton_of_isSMulRegular N M x hx j
      · exact hExt j hj₀ (by simp only [List.length_cons]; omega)
      · exact hExt (j + 1) (by omega) (by simp only [List.length_cons]; omega)
    have := ih (ModuleCat.of R (QuotSMulTop x M)) htail hquot
    exact ext_subsingleton_of_iso_right
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs).symm.toModuleIso i

/-- A regular sequence shorter than the dimension leaves no residue-field
socle in its quotient. -/
theorem regularLocal_quotient_ofList_residue_ext_subsingleton
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs) (i : ℕ)
    (hi : i + rs.length < (maximalIdeal R).spanFinrank) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R))
      (ModuleCat.of R (R ⧸ Ideal.ofList rs)) i) := by
  have hvan := ext_quotient_ofList_subsingleton_of_isWeaklyRegular
    (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) rs hreg i
    (fun j _ hj => regularLocal_residue_ext_subsingleton R j (lt_of_le_of_lt hj hi))
  let e := Submodule.quotEquivOfEq
    (Ideal.ofList rs • (⊤ : Submodule R R)) (Ideal.ofList rs)
    (by rw [smul_eq_mul, Ideal.mul_top])
  exact ext_subsingleton_of_iso_right e.toModuleIso i

/-- The maximal ideal cannot be associated to a quotient by fewer regular
equations than the dimension of a regular local ring. -/
theorem regularLocal_maximalIdeal_not_associated_quotient_ofList
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs)
    (hlen : rs.length < (maximalIdeal R).spanFinrank) :
    maximalIdeal R ∉ associatedPrimes R (R ⧸ Ideal.ofList rs) := by
  have hExt := regularLocal_quotient_ofList_residue_ext_subsingleton R rs hreg 0
    (by simpa using hlen)
  have hhom : Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] (R ⧸ Ideal.ofList rs)) :=
    (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp hExt
  intro hass
  obtain ⟨_, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap
    (maximalIdeal R) (R ⧸ Ideal.ofList rs)).mp hass
  have hfzero : f = 0 := hhom.elim f 0
  have h10 : (1 : R ⧸ maximalIdeal R) = 0 := hf (by simp [hfzero])
  exact one_ne_zero h10

/-- In a regular ring, every associated prime of a quotient by a regular
sequence has height bounded by the number of equations. This bound applies
to all associated primes, not just minimal ones. -/
theorem regularRing_associatedPrime_quotient_ofList_height_le
    (R : Type u) [CommRing R] [IsRegularRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs)
    (P : Ideal R) (hP : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    P.height ≤ rs.length := by
  let := hP.isPrime
  let S := Localization.AtPrime P
  let f := Algebra.linearMap R S
  let I := Ideal.ofList rs
  have hlocal : maximalIdeal S ∈ associatedPrimes S
      (S ⧸ I.localized' S P.primeCompl f) := by
    apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl (I.toLocalizedQuotient' S P.primeCompl f) (maximalIdeal S)
    simpa only [S, Localization.AtPrime.under_maximalIdeal] using hP
  have hI : I.localized' S P.primeCompl f = Ideal.ofList (rs.map (algebraMap R S)) := by
    rw [← Ideal.map_ofList]
    rw [Ideal.map, Ideal.span, Submodule.localized'_eq_span]
    rfl
  rw [hI] at hlocal
  have hregloc := hreg.of_isLocalization S P.primeCompl
  have hle : (maximalIdeal S).spanFinrank ≤ rs.length := by
    by_contra! hlt
    exact regularLocal_maximalIdeal_not_associated_quotient_ofList S
      (rs.map (algebraMap R S)) hregloc (by simpa only [List.length_map] using hlt) hlocal
  have hdim : (P.height : WithBot ℕ∞) ≤ (rs.length : WithBot ℕ∞) := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P S,
      ← IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact_mod_cast hle
  exact_mod_cast hdim

/-- Every prime containing a weakly regular sequence has height at least its
length. Localization makes the sequence regular, and the quotient-dimension
formula gives the bound. -/
theorem length_le_height_of_isWeaklyRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs)
    (P : Ideal R) [P.IsPrime] (hP : Ideal.ofList rs ≤ P) :
    (rs.length : ℕ∞) ≤ P.height := by
  let S := Localization.AtPrime P
  let ss := rs.map (algebraMap R S)
  have hregloc : IsRegular S ss :=
    hreg.isRegular_of_isLocalization_of_mem S P
      (fun r hr => hP (Ideal.subset_span hr))
  have : Nontrivial (S ⧸ Ideal.ofList ss) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    simpa only [smul_eq_mul, Ideal.mul_top] using hregloc.top_ne_smul.symm
  have hdim : (rs.length : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P S]
    have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ss hregloc
    calc
      (rs.length : WithBot ℕ∞) = 0 + ss.length := by simp [ss]
      _ ≤ ringKrullDim (S ⧸ Ideal.ofList ss) + ss.length :=
        add_le_add ringKrullDim_nonneg_of_nontrivial le_rfl
      _ = ringKrullDim S := h
  exact_mod_cast hdim

/-- Complete intersections in a regular ring have no embedded associated
primes. No reducedness or prime-section assumption is required. -/
theorem regularRing_associatedPrime_quotient_ofList_mem_minimalPrimes
    (R : Type u) [CommRing R] [IsRegularRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs)
    (P : Ideal R) (hP : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    P ∈ (Ideal.ofList rs).minimalPrimes := by
  let := hP.isPrime
  have hIP : Ideal.ofList rs ≤ P := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient]
      using hP.annihilator_le
  have hheight := regularRing_associatedPrime_quotient_ofList_height_le R rs hreg P hP
  refine ⟨⟨hP.isPrime, hIP⟩, ?_⟩
  intro Q hQ hQP
  let := hQ.1
  by_contra hPQ
  have hlt : Q < P := lt_of_le_not_ge hQP hPQ
  have hQheight := length_le_height_of_isWeaklyRegular rs hreg Q hQ.2
  have hsucc : (rs.length : ℕ∞) + 1 ≤ (rs.length : ℕ∞) :=
    (add_le_add hQheight le_rfl).trans
      ((Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hheight)
  have hsucc' : rs.length + 1 ≤ rs.length := by exact_mod_cast hsucc
  omega

/-- The unmixedness conclusion stated inside the quotient ring, as required
by the associated-prime witness in Voisin's fixed-component construction. -/
theorem regularRing_quotient_ofList_associatedPrime_mem_minimalPrimes
    (R : Type u) [CommRing R] [IsRegularRing R]
    (rs : List R) (hreg : IsWeaklyRegular R rs)
    (P : Ideal (R ⧸ Ideal.ofList rs))
    (hP : P ∈ associatedPrimes (R ⧸ Ideal.ofList rs) (R ⧸ Ideal.ofList rs)) :
    P ∈ minimalPrimes (R ⧸ Ideal.ofList rs) := by
  let f := Ideal.Quotient.mk (Ideal.ofList rs)
  have hcomap : P.comap f ∈ associatedPrimes R (R ⧸ Ideal.ofList rs) := by
    obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hP
    apply isAssociatedPrime_iff.mpr
    refine ⟨hprime.comap f, x, ?_⟩
    ext r
    simp only [Ideal.mem_comap, hx, Submodule.mem_colon_singleton,
      Submodule.mem_bot, smul_eq_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, f]
  have hmin := regularRing_associatedPrime_quotient_ofList_mem_minimalPrimes R rs hreg
    (P.comap f) hcomap
  refine ⟨⟨hP.isPrime, bot_le⟩, ?_⟩
  intro Q hQ hQP
  apply (Ideal.comap_le_comap_iff_of_surjective f Ideal.Quotient.mk_surjective P Q).mp
  apply hmin.2 ⟨hQ.1.comap f, ?_⟩ (Ideal.comap_mono hQP)
  intro r hr
  change f r ∈ Q
  have hrzero : f r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hrzero]
  exact Q.zero_mem

end PfaffianDescent
