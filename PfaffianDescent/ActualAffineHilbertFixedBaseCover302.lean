import PfaffianDescent.ActualAffineHilbertChartCover302

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u

/-- Construct the literal composed base action at abstract ring dictionaries,
prior to inserting either localization and its original determinant. -/
def fixedBaseCompositePatchAlgebra302
    (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra S T] : Algebra R T :=
  ((algebraMap S T).comp ((algebraMap A S).comp (algebraMap R A))).toAlgebra

/-- Its canonical scalar map is exactly the original three coefficient maps composed. -/
lemma fixedBaseCompositePatchAlgebra_algebraMap302
    (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra S T] :
    letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
    algebraMap R T = (algebraMap S T).comp ((algebraMap A S).comp (algebraMap R A)) := rfl

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}

/-- The SAME original test-family patch is an actual universal289 pullback over fixed R.
Its coefficient point is constructed by inverse287 classification of the literal whole ideal. -/
lemma actualAffineHilbertPoint_fixedBasePatch_isUniversal302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    let S := Localization.Away i.1
    let T := Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
    letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
    ∃ p : UniversalCyclicCoefficientAlgebra282 R m n q.val.1 q.val.2 →ₐ[R] T,
      actualAffineHilbertPoint_monomialRestriction302 P I i q =
        cyclicCoefficientUniversalFamilyPullback302 R m n q.val.1 q.val.2 p := by
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
  let x := wholeQuotientMonomialChart_on_cover299
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q
  refine ⟨(cyclicCoefficientWholeIdealChartEquiv287
    (A := T) q.val.1 q.val.2 R q.property).symm x, ?_⟩
  exact (actualAffineHilbertPoint_monomialRestriction_eq_chart302 P I e h i q).trans
    (monomialWholeIdealNativeFamily_isUniversalPullback302 R (A := T)
      q.val.1 q.val.2 q.property x).symm

/-- Arbitrary R-test affine195 families construct one affine cover with fixed-R coefficient points.
No covering, presentation, rank or basis conclusion is assumed; all original ideals are retained. -/
lemma actualAffineHilbertPoint_fixedBaseUniversalMonomialAffineCover302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (hn : 0 < n) :
    ∃ (I : Ideal (MvPolynomial (Fin m) A))
      (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I))),
      ∃ hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
        (Basis (Fin n) (Localization.Away s)
          (MvPolynomial (Fin m) (Localization.Away s) ⧸
            I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))),
      P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      ∃ U : (Spec (.of A)).AffineOpenCover,
        U = localWholeQuotientMonomialAffineCover302 I hb hn ∧
        ∀ (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n),
          let S := Localization.Away i.1
          let T := Localization.Away (wholeIdealMonomialTransitionDet290
            (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
          letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
          ∃ p : UniversalCyclicCoefficientAlgebra282 R m n q.val.1 q.val.2 →ₐ[R] T,
            actualAffineHilbertPoint_monomialRestriction302 P I i q =
              cyclicCoefficientUniversalFamilyPullback302 R m n q.val.1 q.val.2 p := by
  obtain ⟨I, e, h, hb⟩ := actualAffineHilbertPoint_localWholeQuotientBases301 P
  exact ⟨I, e, hb, h, localWholeQuotientMonomialAffineCover302 I hb hn, rfl,
    actualAffineHilbertPoint_fixedBasePatch_isUniversal302 R P I e h⟩

end PfaffianDescent
