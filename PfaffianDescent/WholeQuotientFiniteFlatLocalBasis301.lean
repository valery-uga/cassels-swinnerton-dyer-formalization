import PfaffianDescent.FiniteFlatConstantRankLocalBasis301
import PfaffianDescent.FixedRankWholeQuotientMonomialCover299
import PfaffianDescent.NativeAffineUniversalWholeFamily289

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
variable {A : Type u} [CommRing A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A))

/-- The literal geometric finite-flat degree condition supplies constant module rank. -/
lemma wholeQuotientFiniteFlatDegree_rank301
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))))]
    (hd : ∀ p : PrimeSpectrum A,
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).finrank p = n)
    (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (MvPolynomial (Fin m) A ⧸ I) p = n := by
  letI : Module.Finite A (MvPolynomial (Fin m) A ⧸ I) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).mp inferInstance)
  letI : Module.Flat A (MvPolynomial (Fin m) A ⧸ I) :=
    RingHom.flat_algebraMap_iff.mp ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).mp inferInstance)
  exact (Scheme.Hom.finrank_SpecMap_algebraMap A (MvPolynomial (Fin m) A ⧸ I) p).symm.trans (hd p)

/-- Actual quotient bases on coefficient localizations are constructed from finite-flat degree alone. -/
lemma wholeQuotientFiniteFlatDegree_localBasis301
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))))]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))))]
    (hd : ∀ p : PrimeSpectrum A,
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).finrank p = n)
    (p : PrimeSpectrum A) :
    ∃ s ∉ p.asIdeal, Nonempty
      (Basis (Fin n) (Localization.Away s)
        (MvPolynomial (Fin m) (Localization.Away s) ⧸
          I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))) := by
  letI : Module.Finite A (MvPolynomial (Fin m) A ⧸ I) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).mp inferInstance)
  letI : Module.Flat A (MvPolynomial (Fin m) A ⧸ I) :=
    RingHom.flat_algebraMap_iff.mp ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).mp inferInstance)
  obtain ⟨s, hs, ⟨b⟩⟩ := finiteFlatConstantRank_localTensorBasis301
    (wholeQuotientFiniteFlatDegree_rank301 I hd) p
  exact ⟨s, hs, ⟨b.map (polynomialWholeIdealScalarExtension286 (Localization.Away s) I).toLinearEquiv⟩⟩

end PfaffianDescent
