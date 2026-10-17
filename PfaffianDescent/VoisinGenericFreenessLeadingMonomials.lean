import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.PWO
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Flat.Basic

/-!
# Finite leading exponents for the generic-freeness route

Dickson's lemma gives finite divisibility control of leading monomials of
polynomials in a generic curve ideal. This is the first finite step toward a
Gröbner-style proof of generic freeness for the spread-out coordinate ring.
-/

namespace PfaffianDescent

open MvPolynomial
open Module
open scoped MonomialOrder

universe u

/-- Any set of exponent vectors in finitely many variables has finitely
many minimal elements, and each member lies above one of them. -/
theorem exists_finite_minimal_exponent_cover
    (S : Set (Fin 4 →₀ ℕ)) :
    ∃ T : Set (Fin 4 →₀ ℕ), T.Finite ∧ T ⊆ S ∧
      ∀ e ∈ S, ∃ t ∈ T, t ≤ e := by
  let T : Set (Fin 4 →₀ ℕ) := {e | Minimal (· ∈ S) e}
  have hfinite : T.Finite := by
    exact (setOfPred_minimal_antichain (· ∈ S)).finite_of_wellQuasiOrdered
      wellQuasiOrdered_le
  refine ⟨T, hfinite, ?_, ?_⟩
  · intro e he
    exact he.1
  · intro e he
    obtain ⟨t, hte, ht⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal he
    exact ⟨t, ht, hte⟩

/-- Over a field, finitely many nonzero polynomials in an arbitrary ideal
control divisibility of every leading exponent in that ideal. -/
theorem exists_finite_leading_exponent_cover
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧
        (∀ g ∈ G, g ≠ 0) ∧
        ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f := by
  classical
  let S : Set (Fin 4 →₀ ℕ) :=
    {e | ∃ f : MvPolynomial (Fin 4) F, f ∈ I ∧ f ≠ 0 ∧ m.degree f = e}
  obtain ⟨T, hTfinite, hTS, hcover⟩ := exists_finite_minimal_exponent_cover S
  letI : Finite T := hTfinite.to_subtype
  let g : T → MvPolynomial (Fin 4) F := fun t =>
    Classical.choose (hTS t.property)
  have hg (t : T) : g t ∈ I ∧ g t ≠ 0 ∧ m.degree (g t) = t :=
    Classical.choose_spec (hTS t.property)
  refine ⟨Set.range g, Set.finite_range g, ?_, ?_, ?_⟩
  · rintro q ⟨t, rfl⟩
    exact (hg t).1
  · rintro q ⟨t, rfl⟩
    exact (hg t).2.1
  · intro f hf hne
    obtain ⟨t, ht, htle⟩ := hcover (m.degree f) ⟨f, hf, hne, rfl⟩
    refine ⟨g ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, ?_⟩
    rw [(hg ⟨t, ht⟩).2.2]
    exact htle

/-- The finite leading-exponent cover is a Gröbner-style generating set:
division by it leaves zero remainder for every polynomial in the ideal. -/
theorem exists_finite_leading_division_generators
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧
        (∀ g ∈ G, IsUnit (m.leadingCoeff g)) ∧
        ∀ f ∈ I,
          ∃ q : G →₀ MvPolynomial (Fin 4) F,
            f = Finsupp.linearCombination (MvPolynomial (Fin 4) F)
              (fun g : G => (g : MvPolynomial (Fin 4) F)) q := by
  classical
  obtain ⟨G, hGfinite, hGsub, hGne, hcover⟩ :=
    exists_finite_leading_exponent_cover m I
  have hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := by
    intro g hg
    exact isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr (hGne g hg))
  refine ⟨G, hGfinite, hGsub, hunit, ?_⟩
  intro f hf
  obtain ⟨q, r, heq, _, hrem⟩ := m.div_set hunit f
  have hcomb : Finsupp.linearCombination (MvPolynomial (Fin 4) F)
      (fun g : G => (g : MvPolynomial (Fin 4) F)) q ∈ I := by
    have hspan : Submodule.span (MvPolynomial (Fin 4) F)
        (Set.range (fun g : G => (g : MvPolynomial (Fin 4) F))) ≤ I := by
      apply Submodule.span_le.mpr
      rintro x ⟨g, rfl⟩
      exact hGsub g.property
    apply hspan
    rw [← Finsupp.range_linearCombination]
    exact ⟨q, rfl⟩
  have hrI : r ∈ I := by
    have h := I.sub_mem hf hcomb
    simpa only [heq, add_sub_cancel_left] using h
  have hrzero : r = 0 := by
    by_contra hrne
    obtain ⟨g, hg, hgle⟩ := hcover r hrI hrne
    exact (hrem (m.degree r) (m.degree_mem_support hrne) g hg) hgle
  exact ⟨q, by simpa [hrzero] using heq⟩

/-- An ideal element supported only on monomials not divisible by the
chosen leading exponents must be zero. -/
theorem standard_supported_ideal_element_eq_zero
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f)
    (r : MvPolynomial (Fin 4) F) (hrI : r ∈ I)
    (hstandard : ∀ e ∈ r.support, ∀ g ∈ G, ¬ m.degree g ≤ e) : r = 0 := by
  by_contra hrne
  obtain ⟨g, hg, hgle⟩ := hcover r hrI hrne
  exact (hstandard (m.degree r) (m.degree_mem_support hrne) g hg) hgle

/-- A leading-exponent cover inside an ideal generates that ideal over the
field, provided its leading coefficients are units. -/
theorem ideal_span_eq_of_leading_exponent_cover
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hsub : G ⊆ I)
    (hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) :
    Ideal.span G = I := by
  classical
  apply le_antisymm
  · exact Ideal.span_le.mpr hsub
  · intro f hf
    obtain ⟨q, r, heq, _, hstandard⟩ := m.div_set hunit f
    have hcomb : Finsupp.linearCombination (MvPolynomial (Fin 4) F)
        (fun g : G => (g : MvPolynomial (Fin 4) F)) q ∈ Ideal.span G := by
      have hspan : Submodule.span (MvPolynomial (Fin 4) F)
          (Set.range (fun g : G => (g : MvPolynomial (Fin 4) F))) ≤ Ideal.span G := by
        apply Submodule.span_le.mpr
        rintro x ⟨g, rfl⟩
        exact Ideal.subset_span g.property
      apply hspan
      rw [← Finsupp.range_linearCombination]
      exact ⟨q, rfl⟩
    have hrI : r ∈ I := by
      have h := I.sub_mem hf ((Ideal.span_le.mpr hsub) hcomb)
      simpa only [heq, add_sub_cancel_left] using h
    have hrzero := standard_supported_ideal_element_eq_zero
      m I G hcover r hrI hstandard
    have heq' : f = Finsupp.linearCombination (MvPolynomial (Fin 4) F)
        (fun g : G => (g : MvPolynomial (Fin 4) F)) q := by
      simpa [hrzero] using heq
    rw [heq']
    exact hcomb

/-- The S-polynomial of two elements of an ideal remains in that ideal. -/
theorem sPolynomial_mem_ideal
    {R : Type u} [CommRing R] (m : MonomialOrder (Fin 4))
    (J : Ideal (MvPolynomial (Fin 4) R))
    (f g : MvPolynomial (Fin 4) R) (hf : f ∈ J) (hg : g ∈ J) :
    m.sPolynomial f g ∈ J := by
  rw [m.sPolynomial_def]
  exact J.sub_mem
    (J.mul_mem_left _ hf)
    (J.mul_mem_left _ hg)

/-- Each critical S-polynomial has a bounded division certificate when the
set is a unit-leading cover of the ideal. -/
theorem sPolynomial_division_certificate_of_leading_cover
    {R : Type u} [CommRing R] (m : MonomialOrder (Fin 4))
    (J : Ideal (MvPolynomial (Fin 4) R))
    (G : Set (MvPolynomial (Fin 4) R))
    (hsub : G ⊆ J)
    (hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ f ∈ J, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f)
    (f g : G) :
    ∃ q : G →₀ MvPolynomial (Fin 4) R,
      m.sPolynomial (f : MvPolynomial (Fin 4) R) g =
        Finsupp.linearCombination (MvPolynomial (Fin 4) R)
          (fun a : G => (a : MvPolynomial (Fin 4) R)) q ∧
      (∀ a : G, m.degree ((a : MvPolynomial (Fin 4) R) * q a) ≼[m]
        m.degree (m.sPolynomial (f : MvPolynomial (Fin 4) R) g)) ∧
      (m.sPolynomial (f : MvPolynomial (Fin 4) R) g = 0 ∨
        m.degree (m.sPolynomial (f : MvPolynomial (Fin 4) R) g) ≺[m]
          m.degree (f : MvPolynomial (Fin 4) R) ⊔
            m.degree (g : MvPolynomial (Fin 4) R)) := by
  classical
  let s := m.sPolynomial (f : MvPolynomial (Fin 4) R) g
  have hsJ : s ∈ J := sPolynomial_mem_ideal m J f g (hsub f.property) (hsub g.property)
  obtain ⟨q, r, heq, hdeg, hstandard⟩ := m.div_set hunit s
  have hcomb : Finsupp.linearCombination (MvPolynomial (Fin 4) R)
      (fun a : G => (a : MvPolynomial (Fin 4) R)) q ∈ J := by
    have hspan : Submodule.span (MvPolynomial (Fin 4) R)
        (Set.range (fun a : G => (a : MvPolynomial (Fin 4) R))) ≤ J := by
      apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      exact hsub a.property
    apply hspan
    rw [← Finsupp.range_linearCombination]
    exact ⟨q, rfl⟩
  have hrJ : r ∈ J := by
    have h := J.sub_mem hsJ hcomb
    simpa only [heq, add_sub_cancel_left] using h
  have hr0 := standard_supported_ideal_element_eq_zero
    m J G hcover r hrJ hstandard
  refine ⟨q, ?_, hdeg, ?_⟩
  · simpa [s, hr0] using heq
  · exact (m.degree_sPolynomial (f : MvPolynomial (Fin 4) R)
      (g : MvPolynomial (Fin 4) R)).symm

/-- Two standard-supported representatives of the same ideal quotient
class are equal. -/
theorem standard_supported_representative_unique
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f)
    (r s : MvPolynomial (Fin 4) F)
    (hr : ∀ e ∈ r.support, ∀ g ∈ G, ¬ m.degree g ≤ e)
    (hs : ∀ e ∈ s.support, ∀ g ∈ G, ¬ m.degree g ≤ e)
    (hmod : r - s ∈ I) : r = s := by
  apply sub_eq_zero.mp
  apply standard_supported_ideal_element_eq_zero m I G hcover (r - s) hmod
  intro e he g hg
  rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 4) r s he) with her | hes
  · exact hr e her g hg
  · exact hs e hes g hg

/-- Every polynomial has a unique remainder supported on standard monomials
modulo a finite leading-exponent set for the ideal. -/
theorem exists_finite_unique_standard_remainders
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧
        (∀ g ∈ G, IsUnit (m.leadingCoeff g)) ∧
        (∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) ∧
        ∀ f : MvPolynomial (Fin 4) F,
          ∃! r : MvPolynomial (Fin 4) F,
            f - r ∈ I ∧
              ∀ e ∈ r.support, ∀ g ∈ G, ¬ m.degree g ≤ e := by
  classical
  obtain ⟨G, hGfinite, hGsub, hGne, hcover⟩ :=
    exists_finite_leading_exponent_cover m I
  have hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := by
    intro g hg
    exact isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr (hGne g hg))
  refine ⟨G, hGfinite, hGsub, hunit, hcover, ?_⟩
  intro f
  obtain ⟨q, r, heq, _, hstandard⟩ := m.div_set hunit f
  have hcomb : Finsupp.linearCombination (MvPolynomial (Fin 4) F)
      (fun g : G => (g : MvPolynomial (Fin 4) F)) q ∈ I := by
    have hspan : Submodule.span (MvPolynomial (Fin 4) F)
        (Set.range (fun g : G => (g : MvPolynomial (Fin 4) F))) ≤ I := by
      apply Submodule.span_le.mpr
      rintro x ⟨g, rfl⟩
      exact hGsub g.property
    apply hspan
    rw [← Finsupp.range_linearCombination]
    exact ⟨q, rfl⟩
  have hmod : f - r ∈ I := by
    simpa only [heq, add_sub_cancel_right] using hcomb
  refine ⟨r, ⟨hmod, hstandard⟩, ?_⟩
  intro s hs
  have hrs : r - s ∈ I := by
    have h := I.sub_mem hs.1 hmod
    convert h using 1 <;> ring
  exact (standard_supported_representative_unique m I G hcover r s
    hstandard hs.2 hrs).symm

/-- A generic ideal admits finitely many leading generators together with
bounded division certificates for every critical pair among them. -/
theorem exists_finite_leading_cover_with_critical_pair_certificates
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧ Ideal.span G = I ∧
        (∀ g ∈ G, IsUnit (m.leadingCoeff g)) ∧
        (∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) ∧
        ∃ q : G → G → (G →₀ MvPolynomial (Fin 4) F),
          ∀ f g : G,
            m.sPolynomial (f : MvPolynomial (Fin 4) F) g =
              Finsupp.linearCombination (MvPolynomial (Fin 4) F)
                (fun a : G => (a : MvPolynomial (Fin 4) F)) (q f g) ∧
            ∀ a : G, m.degree ((a : MvPolynomial (Fin 4) F) * (q f g) a) ≼[m]
              m.degree (m.sPolynomial (f : MvPolynomial (Fin 4) F) g) := by
  classical
  obtain ⟨G, hfinite, hsub, hunit, hcover, _⟩ :=
    exists_finite_unique_standard_remainders m I
  have hcert (f g : G) :
      ∃ q : G →₀ MvPolynomial (Fin 4) F,
        m.sPolynomial (f : MvPolynomial (Fin 4) F) g =
          Finsupp.linearCombination (MvPolynomial (Fin 4) F)
            (fun a : G => (a : MvPolynomial (Fin 4) F)) q ∧
        ∀ a : G, m.degree ((a : MvPolynomial (Fin 4) F) * q a) ≼[m]
          m.degree (m.sPolynomial (f : MvPolynomial (Fin 4) F) g) := by
    obtain ⟨q, heq, hdeg, _⟩ :=
      sPolynomial_division_certificate_of_leading_cover
        m I G hsub hunit hcover f g
    exact ⟨q, heq, hdeg⟩
  let q : G → G → (G →₀ MvPolynomial (Fin 4) F) :=
    fun f g => Classical.choose (hcert f g)
  refine ⟨G, hfinite, hsub,
    ideal_span_eq_of_leading_exponent_cover m I G hsub hunit hcover,
    hunit, hcover, q, ?_⟩
  intro f g
  exact Classical.choose_spec (hcert f g)

/-- The polynomials supported on monomials outside the leading-exponent
upward closure form a vector subspace. -/
def standardPolynomialSubmodule
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) :
    Submodule F (MvPolynomial (Fin 4) F) where
  carrier := {r | ∀ e ∈ r.support, ∀ g ∈ G, ¬ m.degree g ≤ e}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs e he g hg
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with her | hes
    · exact hr e her g hg
    · exact hs e hes g hg
  smul_mem' := by
    intro a r hr e he g hg
    exact hr e (MvPolynomial.support_smul he) g hg

/-- An ideal with leading-exponent cover has no nonzero element in the
standard polynomial subspace. -/
theorem standardPolynomialSubmodule_inf_ideal_eq_bot
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F))
    (G : Set (MvPolynomial (Fin 4) F))
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) :
    standardPolynomialSubmodule m G ⊓ Submodule.restrictScalars F I = ⊥ := by
  apply le_antisymm
  · intro r hr
    have hzero := standard_supported_ideal_element_eq_zero
      m I G hcover r hr.2 hr.1
    simpa [hzero]
  · exact bot_le

/-- For a finite leading-exponent cover, the standard-polynomial subspace
and the ideal form complementary vector subspaces of the polynomial ring. -/
theorem exists_finite_standardPolynomialSubmodule_complement
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧ Ideal.span G = I ∧
        (∀ g ∈ G, IsUnit (m.leadingCoeff g)) ∧
        standardPolynomialSubmodule m G ⊓ Submodule.restrictScalars F I = ⊥ ∧
        standardPolynomialSubmodule m G ⊔ Submodule.restrictScalars F I = ⊤ := by
  obtain ⟨G, hGfinite, hGsub, hunit, hcover, hnormal⟩ :=
    exists_finite_unique_standard_remainders m I
  refine ⟨G, hGfinite, hGsub,
    ideal_span_eq_of_leading_exponent_cover m I G hGsub hunit hcover, hunit,
    standardPolynomialSubmodule_inf_ideal_eq_bot m I G hcover, ?_⟩
  apply top_unique
  intro f _
  obtain ⟨r, ⟨hmod, hstandard⟩, _⟩ := hnormal f
  have hsup := Submodule.add_mem_sup
    (S := standardPolynomialSubmodule m G)
    (T := Submodule.restrictScalars F I) hstandard hmod
  convert hsup using 1 <;> ring

/-- The quotient by any polynomial ideal is linearly equivalent to its
standard-polynomial subspace for a finite leading-exponent cover. -/
theorem exists_finite_standardPolynomial_quotientEquiv
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧
        Nonempty ((MvPolynomial (Fin 4) F ⧸ Submodule.restrictScalars F I) ≃ₗ[F]
          standardPolynomialSubmodule m G) := by
  obtain ⟨G, hfinite, hsub, _, _, hinf, hsup⟩ :=
    exists_finite_standardPolynomialSubmodule_complement m I
  refine ⟨G, hfinite, hsub, ?_⟩
  exact ⟨(Submodule.restrictScalars F I).quotientEquivOfIsCompl
    (standardPolynomialSubmodule m G) (IsCompl.of_eq hinf hsup).symm⟩

/-- The standard exponents are precisely those outside the upward closure
of the leading exponents of `G`. -/
def standardExponents {F : Type u} [CommRing F]
    (m : MonomialOrder (Fin 4)) (G : Set (MvPolynomial (Fin 4) F)) :
    Set (Fin 4 →₀ ℕ) :=
  {e | ∀ g ∈ G, ¬ m.degree g ≤ e}

/-- The standard-polynomial subspace is Mathlib's supported-polynomial
submodule, which has a canonical basis of standard monomials. -/
theorem standardPolynomialSubmodule_eq_restrictSupport
    {F : Type u} [CommRing F] (m : MonomialOrder (Fin 4))
    (G : Set (MvPolynomial (Fin 4) F)) :
    standardPolynomialSubmodule m G =
      MvPolynomial.restrictSupport F (standardExponents m G) := by
  ext r
  rfl

/-- A vector of the supported-polynomial basis is the corresponding monomial. -/
theorem basisRestrictSupport_apply_coe
    {F : Type u} [CommRing F] (s : Set (Fin 4 →₀ ℕ)) (e : s) :
    ((MvPolynomial.basisRestrictSupport F s) e : MvPolynomial (Fin 4) F) =
      MvPolynomial.monomial e 1 := by
  change ((AddMonoidAlgebra.supportedEquivFinsupp (R := F) (S := F) s).symm
    (Finsupp.single e 1) : MvPolynomial (Fin 4) F) = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp,
    Finsupp.supportedEquivFinsupp_symm_single, MvPolynomial.single_eq_monomial]

/-- A unit-leading cover over any commutative ring makes the standard
monomial classes a basis of the ideal quotient. This is the criterion to
apply after localizing the coefficient domain. -/
theorem standardMonomial_quotientBasis_of_unit_leading_cover
    {R : Type u} [CommRing R] (m : MonomialOrder (Fin 4))
    (J : Ideal (MvPolynomial (Fin 4) R))
    (G : Set (MvPolynomial (Fin 4) R))
    (hsub : G ⊆ J)
    (hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ f ∈ J, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) :
    ∃ b : Basis (standardExponents m G) R
        (MvPolynomial (Fin 4) R ⧸ Submodule.restrictScalars R J),
      ∀ e, b e = (Submodule.restrictScalars R J).mkQ
        (MvPolynomial.monomial e 1) := by
  classical
  let S := standardPolynomialSubmodule m G
  let q := Submodule.restrictScalars R J
  have hspan : Ideal.span G = J :=
    ideal_span_eq_of_leading_exponent_cover m J G hsub hunit hcover
  have hinf : S ⊓ q = ⊥ :=
    standardPolynomialSubmodule_inf_ideal_eq_bot m J G hcover
  have hsup : S ⊔ q = ⊤ := by
    apply top_unique
    intro f _
    obtain ⟨p, r, heq, _, hstandard⟩ := m.div_set hunit f
    have hcomb : Finsupp.linearCombination (MvPolynomial (Fin 4) R)
        (fun g : G => (g : MvPolynomial (Fin 4) R)) p ∈ J := by
      rw [← hspan]
      have hle : Submodule.span (MvPolynomial (Fin 4) R)
          (Set.range (fun g : G => (g : MvPolynomial (Fin 4) R))) ≤ Ideal.span G := by
        apply Submodule.span_le.mpr
        rintro x ⟨g, rfl⟩
        exact Ideal.subset_span g.property
      apply hle
      rw [← Finsupp.range_linearCombination]
      exact ⟨p, rfl⟩
    have hmod : f - r ∈ J := by
      simpa only [heq, add_sub_cancel_right] using hcomb
    have hs : r + (f - r) ∈ S ⊔ q :=
      Submodule.add_mem_sup hstandard hmod
    convert hs using 1 <;> ring
  have hc : IsCompl q S := (IsCompl.of_eq hinf hsup).symm
  change IsCompl q (standardPolynomialSubmodule m G) at hc
  rw [standardPolynomialSubmodule_eq_restrictSupport m G] at hc
  let e := q.quotientEquivOfIsCompl
    (MvPolynomial.restrictSupport R (standardExponents m G)) hc
  let b : Basis (standardExponents m G) R
      (MvPolynomial (Fin 4) R ⧸ q) :=
    (MvPolynomial.basisRestrictSupport R (standardExponents m G)).map e.symm
  refine ⟨b, ?_⟩
  intro a
  change e.symm.toLinearMap ((MvPolynomial.basisRestrictSupport R
    (standardExponents m G)) a) = q.mkQ (MvPolynomial.monomial a 1)
  rw [show e.symm.toLinearMap = q.mkQ ∘ₗ
      (MvPolynomial.restrictSupport R (standardExponents m G)).subtype from
    Submodule.toLinearMap_symm_quotientEquivOfIsCompl hc]
  simp [basisRestrictSupport_apply_coe]

/-- A unit-leading cover also proves flatness of the polynomial quotient
over its coefficient ring, since the standard monomials form a free basis. -/
theorem polynomialQuotient_flat_of_unit_leading_cover
    {R : Type u} [CommRing R] (m : MonomialOrder (Fin 4))
    (J : Ideal (MvPolynomial (Fin 4) R))
    (G : Set (MvPolynomial (Fin 4) R))
    (hsub : G ⊆ J)
    (hunit : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hcover : ∀ f ∈ J, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f) :
    Module.Flat R (MvPolynomial (Fin 4) R ⧸ Submodule.restrictScalars R J) := by
  obtain ⟨b, _⟩ := standardMonomial_quotientBasis_of_unit_leading_cover
    m J G hsub hunit hcover
  letI : Module.Free R (MvPolynomial (Fin 4) R ⧸
      Submodule.restrictScalars R J) := Module.Free.of_basis b
  infer_instance

/-- An arbitrary polynomial ideal over a field has a finite leading set
whose standard monomials form a basis of its quotient. -/
theorem exists_finite_standardMonomial_quotientBasis
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧
        Nonempty (Basis (standardExponents m G) F
          (MvPolynomial (Fin 4) F ⧸ Submodule.restrictScalars F I)) := by
  obtain ⟨G, hfinite, hsub, ⟨e⟩⟩ :=
    exists_finite_standardPolynomial_quotientEquiv m I
  refine ⟨G, hfinite, hsub, ?_⟩
  rw [standardPolynomialSubmodule_eq_restrictSupport m G] at e
  exact ⟨(MvPolynomial.basisRestrictSupport (R := F) (standardExponents m G)).map e.symm⟩

/-- The basis vectors of the generic quotient are exactly the classes of
the standard monomials, not merely vectors indexed by standard exponents. -/
theorem exists_finite_standardMonomial_quotientBasis_spec
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧ Ideal.span G = I ∧
        ∃ b : Basis (standardExponents m G) F
            (MvPolynomial (Fin 4) F ⧸ Submodule.restrictScalars F I),
          ∀ e, b e = (Submodule.restrictScalars F I).mkQ
            (MvPolynomial.monomial e 1) := by
  obtain ⟨G, hfinite, hsub, hspan, _, hinf, hsup⟩ :=
    exists_finite_standardPolynomialSubmodule_complement m I
  let q := Submodule.restrictScalars F I
  have hc : IsCompl q (standardPolynomialSubmodule m G) :=
    (IsCompl.of_eq hinf hsup).symm
  rw [standardPolynomialSubmodule_eq_restrictSupport m G] at hc
  let e := q.quotientEquivOfIsCompl
    (MvPolynomial.restrictSupport F (standardExponents m G)) hc
  let b : Basis (standardExponents m G) F
      (MvPolynomial (Fin 4) F ⧸ q) :=
    (MvPolynomial.basisRestrictSupport F (standardExponents m G)).map e.symm
  refine ⟨G, hfinite, hsub, hspan, b, ?_⟩
  intro a
  change e.symm ((MvPolynomial.basisRestrictSupport F (standardExponents m G)) a) =
    q.mkQ (MvPolynomial.monomial a 1)
  change e.symm.toLinearMap ((MvPolynomial.basisRestrictSupport F
    (standardExponents m G)) a) = q.mkQ (MvPolynomial.monomial a 1)
  rw [show e.symm.toLinearMap = q.mkQ ∘ₗ
      (MvPolynomial.restrictSupport F (standardExponents m G)).subtype from
    Submodule.toLinearMap_symm_quotientEquivOfIsCompl hc]
  simp [basisRestrictSupport_apply_coe]

end PfaffianDescent
