import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Regular.IsSMulRegular
import PfaffianDescent.VoisinRegularSequenceCriteria

/-!
# General sections avoiding associated components

The algebraic core of the generic-section argument is prime avoidance in a
finite-dimensional linear system.  Over an infinite field, a finite union of
proper linear subspaces cannot fill the system.  Since the zero divisors in a
Noetherian ring are the union of its associated primes, any linear system
which is not contained in an associated prime contains a non-zero-divisor.
-/

namespace PfaffianDescent

open Module

section FiniteUnion

variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

/- A finite collection of proper linear subspaces can be avoided by one
vector.  This is the projective-parameter form of the base-locus argument:
each bad locus is a proper linear condition, so their finite union cannot be
the whole section space. -/
theorem exists_vector_avoiding_finite_submodules {ι : Type*} [Finite ι]
    (bad : ι → Submodule K V) (hbad : ∀ i, bad i ≠ ⊤) :
    ∃ v : V, ∀ i, v ∉ bad i := by
  exact Submodule.exists_forall_notMem_of_forall_ne_top bad hbad

end FiniteUnion

section Ring

variable {K R : Type*} [Field K] [Infinite K] [CommRing R]
  [Algebra K R] [IsNoetherianRing R]

/- A witness outside an ideal makes its restriction to a finite-dimensional
linear system a proper submodule.  This is the linear-algebra form of the
base-locus noncontainment condition used in Voisin's argument. -/
theorem finrank_restrict_lt_of_exists_mem_not_mem
    (I : Ideal R) (W : Submodule K R) [FiniteDimensional K W]
    (hnot : ∃ w ∈ W, w ∉ I) :
    Module.finrank K ((I.restrictScalars K).comap W.subtype) <
      Module.finrank K W := by
  let bad : Submodule K W := (I.restrictScalars K).comap W.subtype
  have hlt : bad < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    obtain ⟨w, hwW, hwI⟩ := hnot
    have hwbad : (⟨w, hwW⟩ : W) ∈ bad := by
      rw [htop]
      exact Submodule.mem_top
    exact hwI hwbad
  have hfin := Submodule.finrank_lt_finrank_of_lt hlt
  simpa [bad] using hfin

theorem finrank_comap_lt_of_exists_mem_not_mem
    {M : Type*} [AddCommGroup M] [Module K M]
    (P W : Submodule K M) [FiniteDimensional K W]
    (hnot : ∃ w ∈ W, w ∉ P) :
    Module.finrank K (P.comap W.subtype) < Module.finrank K W := by
  let bad : Submodule K W := P.comap W.subtype
  have hlt : bad < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    obtain ⟨w, hwW, hwP⟩ := hnot
    have hwbad : (⟨w, hwW⟩ : W) ∈ bad := by
      rw [htop]
      exact Submodule.mem_top
    exact hwP hwbad
  have hfin := Submodule.finrank_lt_finrank_of_lt hlt
  simpa [bad] using hfin

theorem finrank_drop_of_avoids_associatedPrimes
    (W : Submodule K R) [FiniteDimensional K W]
    (havoid : ∀ P ∈ associatedPrimes R R, ∃ w ∈ W, w ∉ P) :
    ∀ P ∈ associatedPrimes R R,
      Module.finrank K ((P.restrictScalars K).comap W.subtype) <
        Module.finrank K W := by
  intro P hP
  exact finrank_restrict_lt_of_exists_mem_not_mem P W (havoid P hP)

theorem finrank_drop_of_avoids_associatedPrimes_mod_ideal
    (I : Ideal R) (W : Submodule K R) [FiniteDimensional K W]
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ w ∈ W, Ideal.Quotient.mk I w ∉ P) :
    let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
    let V : Submodule K (R ⧸ I) := W.map q
    ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      Module.finrank K ((P.restrictScalars K).comap V.subtype) <
        Module.finrank K V := by
  let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (R ⧸ I) := W.map q
  letI : FiniteDimensional K V := by
    dsimp [V]
    infer_instance
  dsimp only [q, V]
  intro P hP
  obtain ⟨w, hwW, hwP⟩ := havoid P hP
  apply finrank_comap_lt_of_exists_mem_not_mem
    (P.restrictScalars K) V
  exact ⟨Ideal.Quotient.mk I w, ⟨w, hwW, rfl⟩, hwP⟩

/-- For a finite-dimensional linear system modulo an ideal, associated-prime
avoidance is exactly the strict finite-rank drop of its image on every
associated component.  This lets geometric noncontainment arguments and the
linear-algebraic regular-section selectors be used interchangeably. -/
theorem avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (I : Ideal R) (W : Submodule K R) [FiniteDimensional K W] :
    (∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ w ∈ W, Ideal.Quotient.mk I w ∉ P) ↔
    (let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
    let V : Submodule K (R ⧸ I) := W.map q
    ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      Module.finrank K ((P.restrictScalars K).comap V.subtype) <
        Module.finrank K V) := by
  constructor
  · exact finrank_drop_of_avoids_associatedPrimes_mod_ideal I W
  · intro h P hP
    let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
    let V : Submodule K (R ⧸ I) := W.map q
    have hdrop : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V := by
      simpa only [q, V] using h
    by_contra hnot
    push Not at hnot
    have hsub : V ≤ P.restrictScalars K := by
      rintro z ⟨w, hw, rfl⟩
      exact hnot w hw
    have htop : (P.restrictScalars K).comap V.subtype = ⊤ := by
      apply top_unique
      rintro z hz
      exact hsub z.property
    have hlt := hdrop P hP
    rw [htop] at hlt
    simpa using hlt

/- In a Noetherian domain the associated primes of the ring itself collapse
to the zero ideal.  This is the ring-theoretic form of the fact that every
nonzero element is a non-zero-divisor. -/
theorem associatedPrimes_eq_bot_of_domain
    [Nontrivial R] [NoZeroDivisors R] :
    ∀ P ∈ associatedPrimes R R, P = ⊥ := by
  intro P hP
  apply le_antisymm
  · intro y hy
    have hyunion : y ∈ ⋃ Q ∈ associatedPrimes R R, (Q : Set R) := by
      exact Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at hyunion
    have hynot : ¬ y ∈ nonZeroDivisors R :=
      (Set.mem_compl_iff _ _).mp hyunion
    rw [mem_nonZeroDivisors_iff_ne_zero] at hynot
    exact (not_ne_iff.mp hynot)
  · exact bot_le

/- In a domain, every nonzero finite-dimensional linear system has a strict
   rank drop at the (unique) associated prime.  This is the codimension form
   of the ambient domain argument and is useful when a quotient by a chosen
   equation is itself known to be a domain. -/
theorem finrank_drop_of_domain_nonzero_submodule
    [Nontrivial R] [NoZeroDivisors R]
    (W : Submodule K R) [FiniteDimensional K W] (hW : W ≠ ⊥) :
    ∀ P ∈ associatedPrimes R R,
      Module.finrank K ((P.restrictScalars K).comap W.subtype) <
        Module.finrank K W := by
  intro P hP
  have hP0 : P = ⊥ := associatedPrimes_eq_bot_of_domain P hP
  subst P
  have hcomap : ((⊥ : Ideal R).restrictScalars K).comap W.subtype = ⊥ := by
    apply le_antisymm
    · intro w hw
      exact (show (w : W) = 0 from Subtype.ext (by simpa using hw))
    · exact bot_le
  rw [hcomap]
  have hne : ∃ w : W, w ≠ 0 := by
    by_contra h
    apply hW
    apply le_antisymm
    · intro w hw
      by_contra hwne
      have hwsub : (⟨w, hw⟩ : W) ≠ 0 := by
        intro hz
        apply hwne
        rw [show w = 0 from congrArg Subtype.val hz]
        exact Submodule.zero_mem _
      exact h ⟨⟨w, hw⟩, hwsub⟩
    · exact bot_le
  letI : Nontrivial W :=
    nontrivial_of_ne (Classical.choose hne) 0 (Classical.choose_spec hne)
  have hpos : 0 < Module.finrank K W := Module.finrank_pos
  simpa using hpos

/- Any nonzero finite-dimensional linear system in a domain contains a
non-zero-divisor, without a separate associated-prime avoidance hypothesis. -/
theorem exists_mem_nonZeroDivisors_of_nonzero_submodule
    [Nontrivial R] [NoZeroDivisors R]
    (W : Submodule K R) (hW : W ≠ ⊥) :
    ∃ w ∈ W, w ∈ nonZeroDivisors R := by
  have hnot : ¬ ∀ w : W, w = 0 := by
    intro hall
    apply hW
    apply le_antisymm
    · intro w hw
      have hw0 : (w : R) = 0 := congrArg Subtype.val (hall ⟨w, hw⟩)
      simpa [hw0] using hw
    · exact bot_le
  obtain ⟨w, hw⟩ := not_forall.mp hnot
  refine ⟨w.1, w.2, ?_⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hw0
  exact hw (Subtype.ext hw0)

/-- A linear system which is not contained in any associated prime contains
an element which is a non-zero-divisor. -/
theorem exists_mem_nonZeroDivisors_of_avoids_associatedPrimes
    (W : Submodule K R)
    (havoid : ∀ P ∈ associatedPrimes R R, ∃ w ∈ W, w ∉ P) :
    ∃ w ∈ W, w ∈ nonZeroDivisors R := by
  let ι := {P : Ideal R // P ∈ associatedPrimes R R}
  letI : Finite ι := associatedPrimes.finite R R
  let bad : ι → Submodule K W := fun P ↦
    (P.1.restrictScalars K).comap W.subtype
  have hbad : ∀ P, bad P ≠ ⊤ := by
    intro P htop
    obtain ⟨w, hwW, hwP⟩ := havoid P.1 P.2
    have hwtop : (⟨w, hwW⟩ : W) ∈ bad P := by
      rw [htop]
      exact Submodule.mem_top
    exact hwP hwtop
  obtain ⟨w, hw⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨w.1, w.2, ?_⟩
  have hnot : w.1 ∉ ⋃ P ∈ associatedPrimes R R, (P : Set R) := by
    intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨P, hP⟩ := hmem
    obtain ⟨hPassociated, hwP⟩ := hP
    exact hw ⟨P, hPassociated⟩ hwP
  rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors R] at hnot
  change w.1 ∈ (nonZeroDivisors R : Set R)
  simpa only [Set.mem_compl_iff, not_not] using hnot

/- A finite-dimensional codimension estimate is a convenient way to discharge
the avoidance premise above.  The submodule cut out by an associated prime
is the restriction of that prime to the chosen linear system; if its finrank
is strictly smaller, it cannot contain the whole system. -/
theorem exists_mem_nonZeroDivisors_of_finrank_drop
    (W : Submodule K R) [FiniteDimensional K W]
    (hdrop : ∀ P ∈ associatedPrimes R R,
      Module.finrank K ((P.restrictScalars K).comap W.subtype) <
        Module.finrank K W) :
    ∃ w ∈ W, w ∈ nonZeroDivisors R := by
  apply exists_mem_nonZeroDivisors_of_avoids_associatedPrimes W
  intro P hP
  let bad : Submodule K W := (P.restrictScalars K).comap W.subtype
  have hbad : bad ≠ ⊤ := by
    intro htop
    have hfin : Module.finrank K bad = Module.finrank K W := by
      rw [htop, finrank_top]
    exact (Nat.not_lt_of_ge (Nat.le_of_eq hfin.symm))
      (hdrop P hP)
  have hnot : ¬ ∀ w : W, w ∈ bad := by
    intro hall
    apply hbad
    exact top_unique (by
      intro w hw
      exact hall w)
  obtain ⟨w, hw⟩ := not_forall.mp hnot
  refine ⟨w.1, w.2, ?_⟩
  intro hwP
  apply hw
  change w.1 ∈ P
  exact hwP

/- The same codimension criterion applies after passing to a quotient.  The
image of the linear system in the quotient is finite-dimensional, and a
strict drop inside every associated prime gives a multiplier that is regular
modulo the original ideal. -/
theorem exists_regular_mod_ideal_of_finrank_drop
    (I : Ideal R) (W : Submodule K R) [FiniteDimensional K W]
    (hdrop :
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ w ∈ W, ∀ x : R, w * x ∈ I → x ∈ I := by
  let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (R ⧸ I) := W.map q
  have hVdrop : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      Module.finrank K ((P.restrictScalars K).comap V.subtype) <
        Module.finrank K V := by
    simpa only [q, V] using hdrop
  letI : FiniteDimensional K V := by
    dsimp [V]
    infer_instance
  obtain ⟨y, hyV, hyreg⟩ :=
    exists_mem_nonZeroDivisors_of_finrank_drop V hVdrop
  obtain ⟨w, hwW, hwy⟩ := hyV
  refine ⟨w, hwW, ?_⟩
  intro x hx
  have hzero : Ideal.Quotient.mk I w * Ideal.Quotient.mk I x = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hyreg' : Ideal.Quotient.mk I w ∈ nonZeroDivisors (R ⧸ I) := by
    change q w ∈ nonZeroDivisors (R ⧸ I)
    rw [hwy]
    exact hyreg
  have hxzero : Ideal.Quotient.mk I x = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hyreg').mp hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

/- If the quotient is nontrivial, the same selector retains that its chosen
   representative is nonzero.  This is useful when the selected equation is
   fed into a second principal quotient. -/
theorem exists_regular_mod_ideal_of_finrank_drop_of_ne_top
    (I : Ideal R) (hI : I ≠ ⊤) (W : Submodule K R) [FiniteDimensional K W]
    (hdrop :
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ x : R, w * x ∈ I → x ∈ I := by
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (R ⧸ I) := W.map q
  have hVdrop : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      Module.finrank K ((P.restrictScalars K).comap V.subtype) <
        Module.finrank K V := by
    simpa only [q, V] using hdrop
  letI : FiniteDimensional K V := by
    dsimp [V]
    infer_instance
  obtain ⟨y, hyV, hyreg⟩ :=
    exists_mem_nonZeroDivisors_of_finrank_drop V hVdrop
  obtain ⟨w, hwW, hwy⟩ := hyV
  have hw0 : w ≠ 0 := by
    intro hw
    have hy0 : y = 0 := by
      rw [← hwy]
      simp [hw]
    exact (nonZeroDivisors.ne_zero hyreg) hy0
  refine ⟨w, hwW, hw0, ?_⟩
  intro x hx
  have hzero : Ideal.Quotient.mk I w * Ideal.Quotient.mk I x = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hyreg' : Ideal.Quotient.mk I w ∈ nonZeroDivisors (R ⧸ I) := by
    change q w ∈ nonZeroDivisors (R ⧸ I)
    rw [hwy]
    exact hyreg
  have hxzero : Ideal.Quotient.mk I x = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hyreg').mp hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

theorem exists_regular_mod_ideal_of_avoids_associatedPrimes_finrank
    (I : Ideal R) (W : Submodule K R) [FiniteDimensional K W]
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ w ∈ W, Ideal.Quotient.mk I w ∉ P) :
    ∃ w ∈ W, ∀ x : R, w * x ∈ I → x ∈ I := by
  exact exists_regular_mod_ideal_of_finrank_drop I W
    (finrank_drop_of_avoids_associatedPrimes_mod_ideal I W havoid)

end Ring

section Quotient

variable {K R : Type*} [Field K] [Infinite K] [CommRing R]
  [Algebra K R] [IsNoetherianRing R]

/-- If the image of a linear system modulo `I` avoids every associated
prime, it contains a section whose multiplication is injective modulo `I`.
This is the exact regularity condition used in the three-generator Koszul
complex. -/
theorem exists_regular_mod_ideal_in_linear_system
    (I : Ideal R) (W : Submodule K R)
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ w ∈ W, Ideal.Quotient.mk I w ∉ P) :
    ∃ w ∈ W, ∀ x : R, w * x ∈ I → x ∈ I := by
  let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (R ⧸ I) := W.map q
  have hV : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ y ∈ V, y ∉ P := by
    intro P hP
    obtain ⟨w, hwW, hwP⟩ := havoid P hP
    exact ⟨Ideal.Quotient.mk I w, ⟨w, hwW, rfl⟩, hwP⟩
  obtain ⟨y, hyV, hyreg⟩ :=
    exists_mem_nonZeroDivisors_of_avoids_associatedPrimes V hV
  obtain ⟨w, hwW, hwy⟩ := hyV
  refine ⟨w, hwW, ?_⟩
  intro x hx
  have hzero : Ideal.Quotient.mk I w * Ideal.Quotient.mk I x = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  have hyreg' : Ideal.Quotient.mk I w ∈ nonZeroDivisors (R ⧸ I) := by
    change q w ∈ nonZeroDivisors (R ⧸ I)
    rw [hwy]
    exact hyreg
  have hxzero : Ideal.Quotient.mk I x = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hyreg').mp hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

/- A finite family of quotient rank-drop conditions can be discharged by one
section of the common linear system.  The bad subspaces are indexed by the
associated primes of all quotients at once; finite prime avoidance then gives
a single section which is regular modulo every member of the family. -/
theorem exists_regular_mod_ideal_of_finrank_drop_family
    {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (W : Submodule K R) [FiniteDimensional K W]
    (hdrop : ∀ i : ι,
      let q : R →ₗ[K] R ⧸ I i := (Ideal.Quotient.mkₐ K (I i)).toLinearMap
      let V : Submodule K (R ⧸ I i) := W.map q
      ∀ P ∈ associatedPrimes (R ⧸ I i) (R ⧸ I i),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ w ∈ W, ∀ i : ι, ∀ x : R, w * x ∈ I i → x ∈ I i := by
  let q : ∀ i : ι, R →ₗ[K] R ⧸ I i := fun i =>
    (Ideal.Quotient.mkₐ K (I i)).toLinearMap
  let V : ∀ i : ι, Submodule K (R ⧸ I i) := fun i => W.map (q i)
  let PType : ∀ i : ι, Type _ := fun i =>
    {P : Ideal (R ⧸ I i) // P ∈ associatedPrimes (R ⧸ I i) (R ⧸ I i)}
  let J := Σ i : ι, PType i
  letI : ∀ i : ι, Finite (PType i) := fun i => associatedPrimes.finite _ _
  letI : Finite J := by infer_instance
  let bad : J → Submodule K W := fun j =>
    (j.2.1.restrictScalars K).comap
      ((q j.1).domRestrict W)
  have hbad : ∀ j : J, bad j ≠ ⊤ := by
    intro j htop
    have hdropj := hdrop j.1
    have hdropj' : Module.finrank K
        ((j.2.1.restrictScalars K).comap (V j.1).subtype) <
        Module.finrank K (V j.1) := by
      simpa only [V] using hdropj j.2.1 j.2.2
    have hVnot : ¬ V j.1 ≤ j.2.1.restrictScalars K := by
      intro hle
      have htopV :
          (j.2.1.restrictScalars K).comap (V j.1).subtype = ⊤ := by
        apply top_unique
        intro z hz
        exact hle z.property
      rw [htopV, finrank_top] at hdropj'
      exact (Nat.lt_irrefl _ hdropj')
    obtain ⟨z, hzV, hzP⟩ : ∃ z : R ⧸ I j.1, z ∈ V j.1 ∧ z ∉ j.2.1 := by
      by_contra h
      push Not at h
      exact hVnot (by
        rintro z hz
        exact h z hz)
    obtain ⟨w, hwW, hwq⟩ := hzV
    apply hzP
    have hbadw : (⟨w, hwW⟩ : W) ∈ bad j := by
      rw [htop]
      exact Submodule.mem_top
    exact hwq ▸ hbadw
  obtain ⟨w, hw⟩ := exists_vector_avoiding_finite_submodules bad hbad
  refine ⟨w.1, w.2, ?_⟩
  intro i x hix
  have havoid : ∀ P ∈ associatedPrimes (R ⧸ I i) (R ⧸ I i),
      q i w ∉ P := by
    intro P hP hPmem
    apply hw ⟨i, ⟨P, hP⟩⟩
    exact hPmem
  have hnot : q i w ∉ ⋃ P ∈ associatedPrimes (R ⧸ I i) (R ⧸ I i),
      (P : Set (R ⧸ I i)) := by
    intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨P, hP⟩ := hmem
    obtain ⟨hPassociated, hPmem⟩ := hP
    exact havoid P hPassociated hPmem
  have hnonzd : q i w ∈ nonZeroDivisors (R ⧸ I i) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at hnot
    change q i w ∈ (nonZeroDivisors (R ⧸ I i) : Set (R ⧸ I i))
    simpa only [Set.mem_compl_iff, not_not] using hnot
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (mul_left_mem_nonZeroDivisors_eq_zero_iff hnonzd).mp
  change Ideal.Quotient.mk (I i) (w.1 * x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hix

/- If the quotient by the ideal is a domain, it is enough to exhibit one
section outside the ideal.  In that case every associated prime consists of
zero-divisors, hence is the zero ideal in the quotient. -/
theorem exists_regular_mod_prime_ideal_of_mem_not_mem
    (I : Ideal R) (hI : I.IsPrime) (W : Submodule K R)
    (hW : ∃ w ∈ W, w ∉ I) :
    ∃ w ∈ W, ∀ x : R, w * x ∈ I → x ∈ I := by
  letI : I.IsPrime := hI
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne_top
  letI : NoZeroDivisors (R ⧸ I) := Ideal.Quotient.noZeroDivisors I
  have hPbot (P : Ideal (R ⧸ I))
      (hP : P ∈ associatedPrimes (R ⧸ I) (R ⧸ I)) : P = ⊥ := by
    apply le_antisymm
    · intro y hy
      have hyunion : y ∈ ⋃ Q ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
          (Q : Set (R ⧸ I)) := by
        exact Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors] at hyunion
      have hynot : ¬ y ∈ nonZeroDivisors (R ⧸ I) :=
        (Set.mem_compl_iff _ _).mp hyunion
      rw [mem_nonZeroDivisors_iff_ne_zero] at hynot
      exact (not_ne_iff.mp hynot)
    · exact bot_le
  have havoid : ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      ∃ w ∈ W, Ideal.Quotient.mk I w ∉ P := by
    intro P hP
    obtain ⟨w, hwW, hwI⟩ := hW
    refine ⟨w, hwW, ?_⟩
    rw [hPbot P hP, Ideal.mem_bot]
    intro hz
    apply hwI
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact exists_regular_mod_ideal_in_linear_system I W havoid

/-- In a prime quotient, every element outside the defining ideal is regular.
This is the form of the third-equation condition supplied by a concrete
noncontainment or Bertini argument. -/
theorem regular_mod_prime_ideal_of_not_mem
    (I : Ideal R) (hI : I.IsPrime) {g : R} (hg : g ∉ I) :
    ∀ x : R, g * x ∈ I → x ∈ I := by
  intro x hx
  exact (hI.mem_or_mem hx).resolve_left hg

/-- For a prime principal ideal, a relatively prime second equation is
regular modulo the first.  If it were zero in the quotient, the first
equation would divide both members of a relatively prime pair and hence be a
unit, contradicting properness of the prime ideal. -/
theorem regular_mod_span_singleton_of_isRelPrime_of_prime
    {f g : R} (hprime : (Ideal.span ({f} : Set R)).IsPrime)
    (hrel : IsRelPrime f g) :
    ∀ x : R, g * x ∈ Ideal.span ({f} : Set R) → x ∈ Ideal.span ({f} : Set R) := by
  intro x hx
  apply (hprime.mem_or_mem hx).resolve_left
  intro hg
  apply hprime.ne_top
  rw [Ideal.span_singleton_eq_top]
  apply hrel (d := f)
  · exact dvd_rfl
  · exact Ideal.mem_span_singleton.mp hg

/- The same prime-quotient specialization feeds directly into the relative
primality condition used by the two-generator Koszul calculation. -/
theorem exists_isRelPrime_in_linear_system_of_prime_ideal
    [IsDomain R] {f : R} (hf : f ≠ 0)
    (hprime : (Ideal.span ({f} : Set R)).IsPrime) (W : Submodule K R)
    (hW : ∃ w ∈ W, w ∉ Ideal.span ({f} : Set R)) :
    ∃ g ∈ W, IsRelPrime f g := by
  obtain ⟨g, hgW, hregular⟩ :=
    exists_regular_mod_prime_ideal_of_mem_not_mem
      (Ideal.span ({f} : Set R)) hprime W hW
  exact ⟨g, hgW, isRelPrime_of_regular_mod_span_singleton hf hregular⟩

/- The prime-quotient selector also returns a representative outside the
   principal ideal.  This strengthened form is useful when the selected
   equation must itself be shown nonzero before entering a second quotient. -/
theorem exists_isRelPrime_and_not_mem_in_linear_system_of_prime_ideal
    [IsDomain R] {f : R} (hf : f ≠ 0)
    (hprime : (Ideal.span ({f} : Set R)).IsPrime) (W : Submodule K R)
    (hW : ∃ w ∈ W, w ∉ Ideal.span ({f} : Set R)) :
    ∃ g ∈ W, g ∉ Ideal.span ({f} : Set R) ∧ IsRelPrime f g := by
  let I := Ideal.span ({f} : Set R)
  obtain ⟨g, hgW, hregular⟩ :=
    exists_regular_mod_prime_ideal_of_mem_not_mem I hprime W hW
  have hgnot : g ∉ I := by
    intro hgI
    have hone : (1 : R) ∈ I := by
      apply hregular 1
      simpa [hgI]
    exact hprime.ne_top ((Ideal.eq_top_iff_one I).mpr hone)
  exact ⟨g, hgW, hgnot, isRelPrime_of_regular_mod_span_singleton hf hregular⟩

/-- Applied to the quotient by one nonzero equation, generic associated-prime
avoidance supplies the relative-primality hypothesis required by the
two-generator Koszul calculation. -/
theorem exists_isRelPrime_in_linear_system_of_avoids_associatedPrimes
    [IsDomain R] {f : R} (hf : f ≠ 0) (W : Submodule K R)
    (havoid : ∀ P ∈ associatedPrimes (R ⧸ (Ideal.span ({f} : Set R)))
      (R ⧸ (Ideal.span ({f} : Set R))),
      ∃ w ∈ W, Ideal.Quotient.mk (Ideal.span ({f} : Set R)) w ∉ P) :
    ∃ g ∈ W, IsRelPrime f g := by
  obtain ⟨g, hgW, hregular⟩ :=
    exists_regular_mod_ideal_in_linear_system
      (Ideal.span ({f} : Set R)) W havoid
  exact ⟨g, hgW, isRelPrime_of_regular_mod_span_singleton hf hregular⟩

/- Composing the two avoidance steps gives a genuine pair of sections: the
first is a non-zero-divisor, and the second is relatively prime to it.  This
is the algebraic form of the first two generic equations in a complete
intersection construction. -/
theorem exists_regular_pair_of_avoids_associatedPrimes
    [IsDomain R] (W₁ W₂ : Submodule K R)
    (havoid₁ : ∀ P ∈ associatedPrimes R R, ∃ w ∈ W₁, w ∉ P)
    (havoid₂ : ∀ (f : R), f ∈ W₁ → f ∈ nonZeroDivisors R →
      ∀ P ∈ associatedPrimes (R ⧸ (Ideal.span ({f} : Set R)))
        (R ⧸ (Ideal.span ({f} : Set R))),
        ∃ w ∈ W₂, Ideal.Quotient.mk (Ideal.span ({f} : Set R)) w ∉ P) :
    ∃ f ∈ W₁, ∃ g ∈ W₂, f ∈ nonZeroDivisors R ∧ IsRelPrime f g := by
  obtain ⟨f, hfW, hfreg⟩ :=
    exists_mem_nonZeroDivisors_of_avoids_associatedPrimes W₁ havoid₁
  have hf0 : f ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp hfreg)
  obtain ⟨g, hgW, hrel⟩ :=
    exists_isRelPrime_in_linear_system_of_avoids_associatedPrimes
      hf0 W₂ (havoid₂ f hfW hfreg)
  exact ⟨f, hfW, g, hgW, hfreg, hrel⟩

/- The two-stage selector also admits a codimension formulation.  The second
rank-drop premise is quantified over the first section because its quotient
depends on the chosen equation. -/
theorem exists_regular_pair_of_finrank_drop
    [IsDomain R] (W₁ W₂ : Submodule K R)
    [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    (hdrop₁ : ∀ P ∈ associatedPrimes R R,
      Module.finrank K ((P.restrictScalars K).comap W₁.subtype) <
        Module.finrank K W₁)
    (hdrop₂ : ∀ (f : R), f ∈ W₁ → f ∈ nonZeroDivisors R →
      let I := Ideal.span ({f} : Set R)
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W₂.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ f ∈ W₁, ∃ g ∈ W₂, f ∈ nonZeroDivisors R ∧ IsRelPrime f g := by
  obtain ⟨f, hfW, hfreg⟩ :=
    exists_mem_nonZeroDivisors_of_finrank_drop W₁ hdrop₁
  have hf0 : f ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hfreg
  obtain ⟨g, hgW, hgreg⟩ :=
    exists_regular_mod_ideal_of_finrank_drop
      (Ideal.span ({f} : Set R)) W₂ (hdrop₂ f hfW hfreg)
  exact ⟨f, hfW, g, hgW, hfreg,
    isRelPrime_of_regular_mod_span_singleton hf0 hgreg⟩

/- In a domain the first-stage rank-drop hypothesis can be replaced by the
weaker assertion that the first linear system is nonzero. -/
theorem exists_regular_pair_of_finrank_drop_of_domain
    [IsDomain R] (W₁ W₂ : Submodule K R)
    [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    (hW₁ : W₁ ≠ ⊥)
    (hdrop₂ : ∀ (f : R), f ∈ W₁ → f ∈ nonZeroDivisors R →
      let I := Ideal.span ({f} : Set R)
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W₂.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ f ∈ W₁, ∃ g ∈ W₂, f ∈ nonZeroDivisors R ∧ IsRelPrime f g := by
  obtain ⟨f, hfW, hfreg⟩ :=
    exists_mem_nonZeroDivisors_of_finrank_drop W₁
      (finrank_drop_of_domain_nonzero_submodule W₁ hW₁)
  have hf0 : f ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hfreg
  obtain ⟨g, hgW, hgreg⟩ :=
    exists_regular_mod_ideal_of_finrank_drop
      (Ideal.span ({f} : Set R)) W₂ (hdrop₂ f hfW hfreg)
  exact ⟨f, hfW, g, hgW, hfreg,
    isRelPrime_of_regular_mod_span_singleton hf0 hgreg⟩

/- The same construction can be iterated once more.  This packages the
three successive codimension estimates needed for a regular complete
intersection, while retaining the exact quotient in which the third section
has to be regular. -/
theorem exists_regular_triple_of_finrank_drop
    [IsDomain R] (W₁ W₂ W₃ : Submodule K R)
    [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    [FiniteDimensional K W₃]
    (hdrop₁ : ∀ P ∈ associatedPrimes R R,
      Module.finrank K ((P.restrictScalars K).comap W₁.subtype) <
        Module.finrank K W₁)
    (hdrop₂ : ∀ (f : R), f ∈ W₁ → f ∈ nonZeroDivisors R →
      let I := Ideal.span ({f} : Set R)
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W₂.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V)
    (hdrop₃ : ∀ (f : R), f ∈ W₁ → f ∈ nonZeroDivisors R →
      ∀ (g : R), g ∈ W₂ → IsRelPrime f g →
      let I := Ideal.span ({f, g} : Set R)
      let q : R →ₗ[K] R ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
      let V : Submodule K (R ⧸ I) := W₃.map q
      ∀ P ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
        Module.finrank K ((P.restrictScalars K).comap V.subtype) <
          Module.finrank K V) :
    ∃ f ∈ W₁, ∃ g ∈ W₂, ∃ h ∈ W₃,
      f ∈ nonZeroDivisors R ∧ IsRelPrime f g ∧
        (∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
          x ∈ Ideal.span ({f, g} : Set R)) := by
  obtain ⟨f, hfW, hfreg⟩ :=
    exists_mem_nonZeroDivisors_of_finrank_drop W₁ hdrop₁
  have hf0 : f ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hfreg
  obtain ⟨g, hgW, hgreg⟩ :=
    exists_regular_mod_ideal_of_finrank_drop
      (Ideal.span ({f} : Set R)) W₂ (hdrop₂ f hfW hfreg)
  have hrel : IsRelPrime f g :=
    isRelPrime_of_regular_mod_span_singleton hf0 hgreg
  obtain ⟨h, hhW, hhreg⟩ :=
    exists_regular_mod_ideal_of_finrank_drop
      (Ideal.span ({f, g} : Set R)) W₃
      (hdrop₃ f hfW hfreg g hgW hrel)
  exact ⟨f, hfW, g, hgW, h, hhW, hfreg, hrel, hhreg⟩

/- Once the first two equations generate a prime intermediate ideal, one
more explicit noncontainment witness selects a third regular equation. -/
theorem exists_regular_third_of_prime_intermediate
    (I : Ideal R) (hI : I.IsPrime) (W : Submodule K R)
    (hW : ∃ w ∈ W, w ∉ I) :
    ∃ w ∈ W, ∀ x : R, w * x ∈ I → x ∈ I :=
  exists_regular_mod_prime_ideal_of_mem_not_mem I hI W hW

end Quotient

end PfaffianDescent
