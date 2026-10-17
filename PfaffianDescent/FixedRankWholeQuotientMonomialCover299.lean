import PfaffianDescent.MonomialBasisContainingOne284
import PfaffianDescent.MonomialWholeIdealChartOverlap290
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry
universe u v

/-- The positive fixed rank gives a genuine monomial basis containing the unit, not just a span. -/
lemma fixedRankPolynomialMonomialBasis_exists299
    {K : Type u} [Field K] {Q : Type v} [CommRing Q] [Algebra K Q] {m n : ℕ}
    (b : Basis (Fin n) K Q) (hn : 0 < n)
    (pi : MvPolynomial (Fin m) K →ₐ[K] Q) (hpi : Function.Surjective pi) :
    ∃ (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (c : Basis (Fin n) K Q),
      B k = 0 ∧ c k = 1 ∧ ∀ j, c j = pi (monomial (B j) 1) := by
  letI : Module.Finite K Q := Module.Finite.of_basis b
  letI : Nontrivial Q := ⟨⟨b ⟨0, hn⟩, 0, b.ne_zero ⟨0, hn⟩⟩⟩
  have hd : Module.finrank K Q = n := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  rw [← hd]
  exact exists_polynomialImageMonomialBasis_containing_one284 pi hpi

variable {A : Type u} [CommRing A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A))
variable (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))

/-- An arbitrary field fiber of the same whole quotient provides a tuple whose determinant is a unit. -/
lemma wholeQuotientFieldFiber_unitDet_exists299
    {K : Type v} [Field K] [Algebra A K] (hn : 0 < n) :
    ∃ (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n), B k = 0 ∧
      IsUnit (algebraMap A K (wholeIdealMonomialTransitionDet290 I b B)) := by
  let J := I.map (MvPolynomial.map (algebraMap A K))
  let bK := wholeIdealScalarBasis290 K I b
  obtain ⟨B, k, c, hk, _, hc⟩ := fixedRankPolynomialMonomialBasis_exists299
    (m := m) (n := n) bK hn (Ideal.Quotient.mkₐ K J) Ideal.Quotient.mk_surjective
  refine ⟨B, k, hk, ?_⟩
  have h : IsUnit (wholeIdealMonomialTransitionDet290 J bK B) :=
    (wholeIdealMonomialTransitionDet_isUnit_iff290 J bK B).mpr ⟨c, hc⟩
  exact (wholeIdealMonomialTransitionDet_baseChange290 (S := K) I b B) ▸ h

/-- The covering determinant outside each prime is constructed through its actual residue-field fiber. -/
lemma wholeQuotient_monomialDet_not_mem_prime299 (hn : 0 < n) (p : PrimeSpectrum A) :
    ∃ (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n), B k = 0 ∧
      wholeIdealMonomialTransitionDet290 I b B ∉ p.asIdeal := by
  obtain ⟨B, k, hk, hu⟩ := wholeQuotientFieldFiber_unitDet_exists299
    (K := p.asIdeal.ResidueField) I b hn
  refine ⟨B, k, hk, ?_⟩
  intro hmem
  have hz : algebraMap A p.asIdeal.ResidueField (wholeIdealMonomialTransitionDet290 I b B) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hmem
  exact hu.ne_zero hz

/-- The chart indices are actual monomial tuples with a designated exponent zero. -/
def MonomialBasisOpenIndex299 (m n : ℕ) :=
  {q : (Fin n → (Fin m →₀ ℕ)) × Fin n // q.1 q.2 = 0}

lemma wholeQuotientMonomialBasisOpens_cover299 (hn : 0 < n) :
    (⨆ q : MonomialBasisOpenIndex299 m n,
      PrimeSpectrum.basicOpen (wholeIdealMonomialTransitionDet290 I b q.val.1)) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro p
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨B, k, hk, hnot⟩ := wholeQuotient_monomialDet_not_mem_prime299 I b hn p
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨(B, k), hk⟩, (PrimeSpectrum.mem_basicOpen _ p).mpr hnot⟩

/-- The determinant elements themselves generate the unit ideal; no covering hypothesis is supplied. -/
lemma wholeQuotientMonomialDeterminants_span_top299 (hn : 0 < n) :
    Ideal.span (Set.range (fun q : MonomialBasisOpenIndex299 m n =>
      wholeIdealMonomialTransitionDet290 I b q.val.1)) = ⊤ := by
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
  letI : P.IsMaximal := hP
  obtain ⟨B, k, hk, hnot⟩ := wholeQuotient_monomialDet_not_mem_prime299 I b hn
    (⟨P, inferInstance⟩ : PrimeSpectrum A)
  apply hnot
  apply hle
  exact Ideal.subset_span ⟨⟨(B, k), hk⟩, rfl⟩

/-- A genuine affine open cover by the determinant localizations of the original coefficient scheme. -/
def wholeQuotientMonomialBasisAffineCover299 (hn : 0 < n) :
    (Spec (.of A)).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A)
    (fun q : MonomialBasisOpenIndex299 m n => wholeIdealMonomialTransitionDet290 I b q.val.1)
    (wholeQuotientMonomialDeterminants_span_top299 I b hn)

/-- Every cover patch is in the represented monomial chart, on the same extended whole ideal. -/
def wholeQuotientMonomialChart_on_cover299 (q : MonomialBasisOpenIndex299 m n) :
    MonomialWholeIdealChart287
      (A := Localization.Away (wholeIdealMonomialTransitionDet290 I b q.val.1)) q.val.1 :=
  ⟨I.map (MvPolynomial.map (algebraMap A
      (Localization.Away (wholeIdealMonomialTransitionDet290 I b q.val.1)))),
    wholeIdealSecondMonomialBasis_localization290
      (S := Localization.Away (wholeIdealMonomialTransitionDet290 I b q.val.1)) I b q.val.1⟩

end PfaffianDescent
