import PfaffianDescent.VoisinGenericFreenessLeadingMonomials
import PfaffianDescent.VoisinPolynomialGenericSpreading
import PfaffianDescent.VoisinGenericFreenessCoefficientMap

/-!
# Clearing a standard-monomial presentation over a common denominator

The same finite set of generic ideal generators both determines the exact
standard-monomial basis and admits one common coefficient denominator. This
is the generic-fibre data needed before proving a free model on a principal
open of the parameter base.
-/

namespace PfaffianDescent

open MvPolynomial Module
open scoped MonomialOrder

universe u v

/-- A finite S-polynomial identity descends through an injective coefficient
map when both the generators and certificate coefficients have been cleared
by the same scalar. -/
theorem cleared_sPolynomial_identity_descends
    {A : Type u} {F : Type v} [CommRing A] [Field F]
    (φ : A →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (d : A)
    {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin 4) F)
    (g : ι → MvPolynomial (Fin 4) A)
    (q : ι → ι → ι → MvPolynomial (Fin 4) F)
    (c : ι → ι → ι → MvPolynomial (Fin 4) A)
    (hg : ∀ i, MvPolynomial.map φ (g i) = MvPolynomial.C (φ d) * f i)
    (hc : ∀ i j k, MvPolynomial.map φ (c i j k) =
      MvPolynomial.C (φ d) * q i j k)
    (hcert : ∀ i j, m.sPolynomial (f i) (f j) =
      ∑ k, q i j k * f k)
    (i j : ι) :
    m.sPolynomial (g i) (g j) = ∑ k, c i j k * g k := by
  classical
  apply MvPolynomial.map_injective φ hφ
  rw [monomialOrder_sPolynomial_map_cleared_pair φ hφ m d
    (g i) (g j) (f i) (f j) (hg i) (hg j)]
  simp only [map_sum, map_mul, hc, hg]
  rw [hcert i j]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The finite generators controlling the generic quotient's monomial basis
can all be cleared over one nonzero coefficient denominator. Their images
generate the entire generic ideal, rather than just lying in it. -/
theorem exists_standardMonomial_basis_with_cleared_generators
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧ Ideal.span G = I ∧
        ∃ d : A, d ≠ 0 ∧
          ∃ g : G → MvPolynomial (Fin 4) A,
            (∀ x : G, MvPolynomial.map (algebraMap A F) (g x) =
              MvPolynomial.C (algebraMap A F d) * (x : MvPolynomial (Fin 4) F)) ∧
            Ideal.span (Set.range (fun x : G =>
              MvPolynomial.map (algebraMap A F) (g x))) = I ∧
            ∃ b : Basis (standardExponents m G) F
                (MvPolynomial (Fin 4) F ⧸ Submodule.restrictScalars F I),
              ∀ e, b e = (Submodule.restrictScalars F I).mkQ
                (MvPolynomial.monomial e 1) := by
  classical
  obtain ⟨G, hfinite, hsub, hspan, b, hb⟩ :=
    exists_finite_standardMonomial_quotientBasis_spec m I
  letI : Finite G := hfinite.to_subtype
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_polynomials_common_denominator_clear
      (A := A) (F := F) Finset.univ
        (fun x : G => (x : MvPolynomial (Fin 4) F))
  let g : G → MvPolynomial (Fin 4) A :=
    fun x => Classical.choose (hclear x (Finset.mem_univ x))
  have hg : ∀ x : G, MvPolynomial.map (algebraMap A F) (g x) =
      MvPolynomial.C (algebraMap A F d) * (x : MvPolynomial (Fin 4) F) := by
    intro x
    exact Classical.choose_spec (hclear x (Finset.mem_univ x))
  refine ⟨G, hfinite, hsub, hspan, d, hd, g, hg, ?_, b, hb⟩
  have hcleared := ideal_span_cleared_generators_eq
    (fun x : G => (x : MvPolynomial (Fin 4) F)) g d hd hg
  simpa only [Subtype.range_coe, hspan] using hcleared

/-- One nonzero denominator clears both the finite leading generators and
every coefficient polynomial in the finite critical-pair division
certificates. The bounded critical-pair identities remain recorded over the
fraction field for the subsequent localization argument. -/
theorem exists_cleared_critical_pair_certificates
    {A : Type u} {F : Type v}
    [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F]
    (m : MonomialOrder (Fin 4))
    (I : Ideal (MvPolynomial (Fin 4) F)) :
    ∃ G : Set (MvPolynomial (Fin 4) F),
      G.Finite ∧ G ⊆ I ∧ Ideal.span G = I ∧
        (∀ x ∈ G, IsUnit (m.leadingCoeff x)) ∧
        (∀ f ∈ I, f ≠ 0 → ∃ x ∈ G, m.degree x ≤ m.degree f) ∧
        ∃ q : G → G → (G →₀ MvPolynomial (Fin 4) F),
          (∀ f g : G,
            m.sPolynomial (f : MvPolynomial (Fin 4) F) g =
              Finsupp.linearCombination (MvPolynomial (Fin 4) F)
                (fun a : G => (a : MvPolynomial (Fin 4) F)) (q f g) ∧
            ∀ a : G, m.degree ((a : MvPolynomial (Fin 4) F) * (q f g) a) ≼[m]
              m.degree (m.sPolynomial (f : MvPolynomial (Fin 4) F) g)) ∧
          ∃ d : A, d ≠ 0 ∧
            ∃ g : G → MvPolynomial (Fin 4) A,
              ∃ c : G → G → G → MvPolynomial (Fin 4) A,
                (∀ x : G, MvPolynomial.map (algebraMap A F) (g x) =
                  MvPolynomial.C (algebraMap A F d) *
                    (x : MvPolynomial (Fin 4) F)) ∧
                (∀ f h a : G, MvPolynomial.map (algebraMap A F) (c f h a) =
                  MvPolynomial.C (algebraMap A F d) * (q f h) a) ∧
                (∀ x : G, m.degree (g x) =
                  m.degree (x : MvPolynomial (Fin 4) F)) ∧
                (∀ f h a : G,
                  m.degree (g a * c f h a) ≼[m]
                    m.degree (m.sPolynomial (g f) (g h))) ∧
                (∀ x : G, m.leadingCoeff (g x) ≠ 0) ∧
                ∃ e : A, e ≠ 0 ∧
                  (∀ x : G, m.leadingCoeff (g x) ∣ e) ∧
                ∃ t : Finset G, (∀ a : G, a ∈ t) ∧
                  ∀ f h : G,
                    m.sPolynomial (g f) (g h) =
                      ∑ a ∈ t, c f h a * g a := by
  classical
  obtain ⟨G, hfinite, hsub, hspan, hunit, hcover, q, hq⟩ :=
    exists_finite_leading_cover_with_critical_pair_certificates m I
  letI : Finite G := hfinite.to_subtype
  letI : Fintype G := Fintype.ofFinite G
  let p : G ⊕ (G × (G × G)) → MvPolynomial (Fin 4) F
    | .inl x => x
    | .inr (f, (h, a)) => (q f h) a
  obtain ⟨d, hd, hclear⟩ :=
    exists_finite_polynomials_common_denominator_clear
      (A := A) (F := F) Finset.univ p
  let lift (i : G ⊕ (G × (G × G))) : MvPolynomial (Fin 4) A :=
    Classical.choose (hclear i (Finset.mem_univ i))
  let g : G → MvPolynomial (Fin 4) A := fun x => lift (.inl x)
  let c : G → G → G → MvPolynomial (Fin 4) A :=
    fun f h a => lift (.inr (f, (h, a)))
  have hg : ∀ x : G, MvPolynomial.map (algebraMap A F) (g x) =
      MvPolynomial.C (algebraMap A F d) *
        (x : MvPolynomial (Fin 4) F) := by
    intro x
    exact Classical.choose_spec (hclear (.inl x) (Finset.mem_univ _))
  have hc : ∀ f h a : G,
      MvPolynomial.map (algebraMap A F) (c f h a) =
        MvPolynomial.C (algebraMap A F d) * (q f h) a := by
    intro f h a
    exact Classical.choose_spec
      (hclear (.inr (f, (h, a))) (Finset.mem_univ _))
  have hdeg : ∀ x : G, m.degree (g x) =
      m.degree (x : MvPolynomial (Fin 4) F) := by
    intro x
    exact monomialOrder_degree_cleared_lift
      (algebraMap A F) (IsFractionRing.injective A F) m d hd
      (g x) x (hg x)
  have hbound : ∀ f h a : G,
      m.degree (g a * c f h a) ≼[m]
        m.degree (m.sPolynomial (g f) (g h)) := by
    intro f h a
    rw [monomialOrder_degree_mul_cleared_lifts
      (algebraMap A F) (IsFractionRing.injective A F) m d hd
      (g a) (c f h a) a ((q f h) a) (hg a) (hc f h a)]
    rw [monomialOrder_degree_sPolynomial_cleared_lifts
      (algebraMap A F) (IsFractionRing.injective A F) m d hd
      (g f) (g h) f h (hg f) (hg h)]
    exact (hq f h).2 a
  have hlead : ∀ x : G, m.leadingCoeff (g x) ≠ 0 := by
    intro x
    apply m.leadingCoeff_ne_zero_iff.mpr
    intro hx
    have hgeneric : (x : MvPolynomial (Fin 4) F) ≠ 0 :=
      m.leadingCoeff_ne_zero_iff.mp
        (isUnit_iff_ne_zero.mp (hunit x x.property))
    have hdF : algebraMap A F d ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective A F).ne hd
    have hscaled : MvPolynomial.C (algebraMap A F d) *
        (x : MvPolynomial (Fin 4) F) ≠ 0 :=
      mul_ne_zero (MvPolynomial.C_ne_zero.mpr hdF) hgeneric
    exact hscaled (by simpa only [hx, map_zero] using (hg x).symm)
  let e : A := ∏ x : G, m.leadingCoeff (g x)
  have he : e ≠ 0 := by
    unfold e
    exact Finset.prod_ne_zero_iff.mpr (fun x _ => hlead x)
  have hdiv : ∀ x : G, m.leadingCoeff (g x) ∣ e := by
    intro x
    exact Finset.dvd_prod_of_mem (fun y : G => m.leadingCoeff (g y))
      (Finset.mem_univ x)
  refine ⟨G, hfinite, hsub, hspan, hunit, hcover, q, ?_, d, hd, g, c, hg, hc, hdeg, hbound,
    hlead, e, he, hdiv,
    Finset.univ, ?_, ?_⟩
  · intro f h
    exact hq f h
  · intro a
    exact Finset.mem_univ a
  · intro f h
    apply cleared_sPolynomial_identity_descends (algebraMap A F)
      (IsFractionRing.injective A F) m d
      (fun x : G => (x : MvPolynomial (Fin 4) F)) g
      (fun i j k => (q i j) k) c hg hc
    intro i j
    rw [(hq i j).1]
    simp only [Finsupp.linearCombination_apply, smul_eq_mul]
    rw [Finsupp.sum_fintype]
    intro a
    simp

end PfaffianDescent
