import Mathlib.RingTheory.Nullstellensatz
import PfaffianDescent.CoordinateRegularExt
import PfaffianDescent.TwoGeneratorKoszulShortExact
import PfaffianDescent.ArtinianQuotientMaximal
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Ext vanishing at affine closed points

A translation moves every affine closed point to the origin.  The coordinate
regular sequence in three variables can therefore be translated and reindexed
on each dehomogenized projective chart.  Rees' theorem then gives the low
Ext-vanishing needed to exclude a point-supported annihilator of a regular
pair.
-/

namespace PfaffianDescent

open MvPolynomial RingTheory.Sequence
open CategoryTheory Abelian

/-- Translation by an affine point, with the sign chosen so that the image of
`X i` vanishes at that point. -/
noncomputable def mvTranslate {K σ : Type*} [Field K] (a : σ → K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp)

lemma mvTranslate_apply_X {K σ : Type*} [Field K] (a : σ → K) (i : σ) :
    mvTranslate a (MvPolynomial.X i) = MvPolynomial.X i - MvPolynomial.C (a i) := by
  simp [mvTranslate]

abbrev CoordinateRing3 (K : Type*) [CommSemiring K] := MvPolynomial (Fin 3) K
noncomputable abbrev coordinate0_3 (K : Type*) [CommSemiring K] : CoordinateRing3 K :=
  MvPolynomial.X (R := K) 0
noncomputable abbrev coordinate1_3 (K : Type*) [CommSemiring K] : CoordinateRing3 K :=
  MvPolynomial.X (R := K) 1
noncomputable abbrev coordinate2_3 (K : Type*) [CommSemiring K] : CoordinateRing3 K :=
  MvPolynomial.X (R := K) 2

/-- The coordinates of affine three-space form a regular sequence. -/
lemma coordinate_sequence_regular3 {K : Type*} [Field K] :
    IsRegular (CoordinateRing3 K) [coordinate0_3 K, coordinate1_3 K, coordinate2_3 K] := by
  refine ⟨?_, ?_⟩
  · rw [isWeaklyRegular_iff_Fin]
    intro i
    fin_cases i
    · rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro p hp
      have hp0 : MvPolynomial.X (R := K) (0 : Fin 3) * p = 0 := by
        simpa [Ideal.ofList_nil] using hp
      have : p = 0 :=
        (MvPolynomial.isRegular_X (R := K) (n := (0 : Fin 3))).left (by simpa using hp0)
      simpa [Ideal.ofList_nil] using this
    · simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add]
      have hN := coordinate_ofList_smul_top_eq_span (K := K) ([0] : List (Fin 3))
      let e := Submodule.quotEquivOfEq _ _ hN
      exact (e.isSMulRegular_congr (coordinate1_3 K)).mpr
        (coordinate_isSMulRegular_mod_span (K := K)
          (s := ({i | i ∈ ([0] : List (Fin 3))} : Set (Fin 3)))
          (j := (1 : Fin 3)) (by simp))
    · simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add]
      have hN := coordinate_ofList_smul_top_eq_span (K := K) ([0, 1] : List (Fin 3))
      let e := Submodule.quotEquivOfEq _ _ hN
      exact (e.isSMulRegular_congr (coordinate2_3 K)).mpr
        (coordinate_isSMulRegular_mod_span (K := K)
          (s := ({i | i ∈ ([0, 1] : List (Fin 3))} : Set (Fin 3)))
          (j := (2 : Fin 3)) (by simp))
  · intro htop
    have h1 : (1 : CoordinateRing3 K) ∈ Ideal.ofList
        [coordinate0_3 K, coordinate1_3 K, coordinate2_3 K] •
        (⊤ : Submodule (CoordinateRing3 K) (CoordinateRing3 K)) := by
      rw [← htop]
      exact Submodule.mem_top
    have hN := coordinate_ofList_smul_top_eq_span (K := K)
      ([0, 1, 2] : List (Fin 3))
    have h1' : (1 : CoordinateRing3 K) ∈ Ideal.span
        (MvPolynomial.X (R := K) ''
          ({i | i ∈ ([0, 1, 2] : List (Fin 3))} : Set (Fin 3))) := by
      exact hN ▸ h1
    rw [MvPolynomial.mem_ideal_span_X_image] at h1'
    obtain ⟨i, _, hi⟩ := h1' 0 (by simp)
    simp at hi

/-- Reindexing the affine three coordinates along an equivalence preserves
regularity. -/
lemma renamed_coordinate_sequence_regular3 {K σ : Type*} [Field K]
    (e : Fin 3 ≃ σ) :
    IsRegular (MvPolynomial σ K)
      [MvPolynomial.X (R := K) (e 0), MvPolynomial.X (R := K) (e 1),
        MvPolynomial.X (R := K) (e 2)] := by
  let e0 := (MvPolynomial.renameEquiv K e).toRingEquiv
  letI : RingHomInvPair
      (e0 : MvPolynomial (Fin 3) K →+* MvPolynomial σ K)
      (e0.symm : MvPolynomial σ K →+* MvPolynomial (Fin 3) K) :=
    RingHomInvPair.of_ringEquiv e0
  letI : RingHomInvPair
      (e0.symm : MvPolynomial σ K →+* MvPolynomial (Fin 3) K)
      (e0 : MvPolynomial (Fin 3) K →+* MvPolynomial σ K) :=
    RingHomInvPair.of_ringEquiv_symm e0
  let E := e0.toSemilinearEquiv
  have hreg := coordinate_sequence_regular3 (K := K)
  have hcongr := E.isRegular_congr'
    [coordinate0_3 K, coordinate1_3 K, coordinate2_3 K]
  simpa [E, e0, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X] using hcongr.mp hreg

/-- The translated, reindexed coordinates at any affine point form a regular
sequence. -/
lemma shifted_renamed_coordinate_sequence_regular3 {K σ : Type*} [Field K]
    (e : Fin 3 ≃ σ) (a : σ → K) :
    IsRegular (MvPolynomial σ K)
      [MvPolynomial.X (R := K) (e 0) - C (a (e 0)),
        MvPolynomial.X (R := K) (e 1) - C (a (e 1)),
        MvPolynomial.X (R := K) (e 2) - C (a (e 2))] := by
  let e0 := (mvTranslate a).toRingEquiv
  letI : RingHomInvPair
      (e0 : MvPolynomial σ K →+* MvPolynomial σ K)
      (e0.symm : MvPolynomial σ K →+* MvPolynomial σ K) :=
    RingHomInvPair.of_ringEquiv e0
  letI : RingHomInvPair
      (e0.symm : MvPolynomial σ K →+* MvPolynomial σ K)
      (e0 : MvPolynomial σ K →+* MvPolynomial σ K) :=
    RingHomInvPair.of_ringEquiv_symm e0
  let E := e0.toSemilinearEquiv
  have hreg := renamed_coordinate_sequence_regular3 (K := K) e
  have hcongr := E.isRegular_congr'
    [MvPolynomial.X (R := K) (e 0), MvPolynomial.X (R := K) (e 1),
      MvPolynomial.X (R := K) (e 2)]
  simpa [E, e0, mvTranslate_apply_X] using hcongr.mp hreg

/-- The residue module of an affine closed point in a three-variable
polynomial ring has zero Ext into the ambient ring below degree three. -/
lemma point_coordinate3_ext_subsingleton {K σ : Type*} [Field K] [Fintype σ]
    (e : Fin 3 ≃ σ) (a : σ → K) (n : ℕ) (hn : n < 3) :
    Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)) n) := by
  let I : Ideal (MvPolynomial σ K) := MvPolynomial.vanishingIdeal K {a}
  let N := ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K ⧸ I)
  let M := ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)
  let rs : List (MvPolynomial σ K) :=
    [MvPolynomial.X (R := K) (e 0) - C (a (e 0)),
      MvPolynomial.X (R := K) (e 1) - C (a (e 1)),
      MvPolynomial.X (R := K) (e 2) - C (a (e 2))]
  have hreg : IsRegular (MvPolynomial σ K) rs :=
    shifted_renamed_coordinate_sequence_regular3 e a
  have hlt : I • (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K)) < ⊤ := by
    change MvPolynomial.vanishingIdeal K {a} •
      (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K)) < ⊤
    rw [Ideal.smul_top_eq_map]
    simpa using (inferInstance : (MvPolynomial.vanishingIdeal K {a} :
      Ideal (MvPolynomial σ K)).IsMaximal).lt_top
  have hSupp : Module.support (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) ⊆
      PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hmem : ∀ r ∈ rs, r ∈ I := by
    intro r hr
    change r ∈ [MvPolynomial.X (R := K) (e 0) - C (a (e 0)),
      MvPolynomial.X (R := K) (e 1) - C (a (e 1)),
      MvPolynomial.X (R := K) (e 2) - C (a (e 2))] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [show I = MvPolynomial.vanishingIdeal K {a} by rfl,
        MvPolynomial.mem_vanishingIdeal_singleton_iff] <;> simp
  exact ModuleCat.subsingleton_ext_of_exists_isRegular I N hSupp M hlt
    rs hmem hreg n (by simpa [rs] using hn)

/-- The same pointwise Ext vanishing holds for a free rank-two target. -/
lemma point_coordinate3_ext_subsingleton_pair {K σ : Type*} [Field K] [Fintype σ]
    (e : Fin 3 ≃ σ) (a : σ → K) (n : ℕ) (hn : n < 3) :
    Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K × MvPolynomial σ K)) n) := by
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)) n) :=
    point_coordinate3_ext_subsingleton e a n hn
  exact ext_subsingleton_pair


/-- A relatively prime pair in affine three-space has no nonzero element
annihilated by a maximal ideal.  The pointwise Ext calculation supplies the
needed homological vanishing after the Nullstellensatz identifies that ideal
with an affine closed point. -/
lemma twoGenerator_no_maximal_annihilator_algClosed
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (e : Fin 3 ≃ σ) (f g : MvPolynomial σ K)
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    (P : Ideal (MvPolynomial σ K)) (hP : P.IsMaximal)
    (x : MvPolynomial σ K ⧸ Ideal.span ({f, g} : Set (MvPolynomial σ K)))
    (hx : ∀ r ∈ P,
      Ideal.Quotient.mk (Ideal.span ({f, g} : Set (MvPolynomial σ K))) r * x = 0) :
    x = 0 := by
  obtain ⟨a, hPa⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hP)
  subst P
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)) 2) :=
    point_coordinate3_ext_subsingleton e a 2 (by norm_num)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K × MvPolynomial σ K)) 1) :=
    point_coordinate3_ext_subsingleton_pair e a 1 (by norm_num)
  letI : Subsingleton (Ext
      (ModuleCat.of (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ MvPolynomial.vanishingIdeal K {a}))
      (ModuleCat.of (MvPolynomial σ K) (MvPolynomial σ K)) 0) :=
    point_coordinate3_ext_subsingleton e a 0 (by norm_num)
  exact twoGenerator_quotient_no_common_annihilator_of_ext_vanishing hf hrel x hx


/-- In affine three-space, a relatively prime pair followed by an equation
with Artinian total quotient is a sequentially regular triple.  A hypothetical
zero divisor produces an associated prime; Artinianness makes its pullback a
maximal ideal, which the preceding pointwise Ext argument excludes. -/
lemma third_regular_of_pair_relPrime_of_artinian_algClosed
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (e : Fin 3 ≃ σ) (f g h : MvPolynomial σ K)
    (hf : f ≠ 0) (hrel : IsRelPrime f g)
    [IsArtinianRing (MvPolynomial σ K ⧸ Ideal.span ({f, g, h} : Set (MvPolynomial σ K)))]
    (a : MvPolynomial σ K)
    (ha : h * a ∈ Ideal.span ({f, g} : Set (MvPolynomial σ K))) :
    a ∈ Ideal.span ({f, g} : Set (MvPolynomial σ K)) := by
  let I : Ideal (MvPolynomial σ K) := Ideal.span ({f, g} : Set _)
  let A := MvPolynomial σ K ⧸ I
  let x : A := Ideal.Quotient.mk I a
  suffices hxzero : x = 0 by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
  by_contra hxnonzero
  have hxh : Ideal.Quotient.mk I h * x = 0 := by
    change Ideal.Quotient.mk I (h * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hnotreg : Ideal.Quotient.mk I h ∉ nonZeroDivisors A := by
    intro hreg
    apply hxnonzero
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hreg).mp hxh
  have hmemunion : Ideal.Quotient.mk I h ∈
      ⋃ P ∈ associatedPrimes A A, (P : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact hnotreg
  obtain ⟨P, hPassoc, hhP⟩ := Set.mem_iUnion₂.mp hmemunion
  change IsAssociatedPrime P A at hPassoc
  rw [isAssociatedPrime_iff] at hPassoc
  obtain ⟨hPprime, y, hPy⟩ := hPassoc
  let Q : Ideal (MvPolynomial σ K) := P.comap (Ideal.Quotient.mk I)
  have hQprime : Q.IsPrime := by
    dsimp [Q]
    exact Ideal.comap_isPrime _ _
  letI : Q.IsPrime := hQprime
  have hJQ : Ideal.span ({f, g, h} : Set (MvPolynomial σ K)) ≤ Q := by
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl | rfl)
    · change Ideal.Quotient.mk I _ ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
      exact P.zero_mem
    · change Ideal.Quotient.mk I _ ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))]
      exact P.zero_mem
    · exact hhP
  have hQmax : Q.IsMaximal := by
    exact ideal_isMaximal_of_isArtinian_quotient
      (Ideal.span ({f, g, h} : Set (MvPolynomial σ K))) Q hJQ
  have hyann : ∀ r ∈ Q, Ideal.Quotient.mk I r * y = 0 := by
    intro r hr
    have hrP : Ideal.Quotient.mk I r ∈ P := hr
    rw [hPy] at hrP
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hrP
    exact hrP
  have hyzero : y = 0 :=
    twoGenerator_no_maximal_annihilator_algClosed e f g hf hrel Q hQmax y hyann
  apply hPprime.ne_top
  rw [hPy, hyzero]
  simp


/-- The three indices different from a chosen projective coordinate. -/
noncomputable def finThreeEquivCoordinateComplement (j : Fin 4) :
    Fin 3 ≃ {i : Fin 4 // i ≠ j} := by
  have hcard : Fintype.card {i : Fin 4 // i ≠ j} = 3 := by
    rw [Fintype.card_subtype_compl]
    simp
  exact (Fin.castOrderIso hcard.symm).toEquiv.trans
    (Fintype.equivFin {i : Fin 4 // i ≠ j}).symm

end PfaffianDescent
