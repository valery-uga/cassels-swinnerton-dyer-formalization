import PfaffianDescent.NativeWholeIdealTestCoverGluing304

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A))
variable (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
  (Basis (Fin n) (Localization.Away s)
    (MvPolynomial (Fin m) (Localization.Away s) ⧸
      I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))))
variable (hn : 0 < n)

/-- Canonical two-stage action on the literal rings of the internally constructed cover. -/
private def originalMonomialTestCoverAlgebra304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  twoStageTestCoefficientAlgebra304 A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

/-- The SAME fixed-R action used in302, on the SAME original localization ring. -/
private def originalMonomialTestCoverFixedBaseAlgebra304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  fixedBaseCompositePatchAlgebra302 R A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

private lemma originalMonomialTestCover_scalarTower304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalMonomialTestCoverAlgebra304 I hb hn z
    letI : Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalMonomialTestCoverFixedBaseAlgebra304 R I hb hn z
    IsScalarTower R A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  twoStageTestCoefficient_scalarTower304 R A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

/-- The chart index is the actual monomial tuple on the original determinant patch. -/
def originalMonomialTestCoverChartIndex304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    MonomialCoefficientChartIndex300 m n :=
  ⟨z.2.val.1, z.2.val.2, z.2.property⟩

/-- Genuine represented chart data on each patch, with the entire original extended ideal. -/
def originalMonomialTestCoverChart304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    MonomialWholeIdealChart287
      (A := (localWholeQuotientMonomialAffineCover302 I hb hn).X z)
      (originalMonomialTestCoverChartIndex304 I hb hn z).monomials :=
  wholeQuotientMonomialChart_on_cover299
    (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2

/-- This chart ideal is literally the image of I under the canonical composed A action. -/
lemma originalMonomialTestCoverChart_ideal304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalMonomialTestCoverAlgebra304 I hb hn z
    (originalMonomialTestCoverChart304 I hb hn z).val =
      I.map (MvPolynomial.map
        (algebraMap A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z))) :=
  wholeIdealImage_twoStage304 I

/-- Its native test map is the Spec map of that same composed action, not an assumed map law. -/
lemma originalMonomialTestCover_scalarMap304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalMonomialTestCoverAlgebra304 I hb hn z
    (localWholeQuotientMonomialAffineCover302 I hb hn).f z =
      Spec.map (CommRingCat.ofHom
        (algebraMap A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z))) :=
  twoStageTestCoefficientSpecMap304

/-- A genuine global fixed-R morphism from the original affine test base to the SAME H. -/
def originalWholeIdealMonomialGlobalMap304 :
    Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n := by
  let U := localWholeQuotientMonomialAffineCover302 I hb hn
  letI : ∀ z, Algebra A (U.X z) := originalMonomialTestCoverAlgebra304 I hb hn
  letI : ∀ z, Algebra R (U.X z) := originalMonomialTestCoverFixedBaseAlgebra304 R I hb hn
  letI : ∀ z, IsScalarTower R A (U.X z) := originalMonomialTestCover_scalarTower304 R I hb hn
  exact nativeWholeIdealTestCoverMap304 R I U
    (originalMonomialTestCoverChartIndex304 I hb hn)
    (originalMonomialTestCoverChart304 I hb hn)
    (originalMonomialTestCoverChart_ideal304 I hb hn)
    (originalMonomialTestCover_scalarMap304 I hb hn)

/-- Restriction along every original test-cover immersion is exactly its inverse-classifier chart map. -/
lemma originalWholeIdealMonomialGlobalMap_chart304
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalMonomialTestCoverFixedBaseAlgebra304 R I hb hn z
    (localWholeQuotientMonomialAffineCover302 I hb hn).f z ≫
        originalWholeIdealMonomialGlobalMap304 R I hb hn =
      monomialWholeIdealTestChartMap303 R
        (originalMonomialTestCoverChartIndex304 I hb hn z)
        (originalMonomialTestCoverChart304 I hb hn z) := by
  let U := localWholeQuotientMonomialAffineCover302 I hb hn
  letI : ∀ z, Algebra A (U.X z) := originalMonomialTestCoverAlgebra304 I hb hn
  letI : ∀ z, Algebra R (U.X z) := originalMonomialTestCoverFixedBaseAlgebra304 R I hb hn
  letI : ∀ z, IsScalarTower R A (U.X z) := originalMonomialTestCover_scalarTower304 R I hb hn
  exact nativeWholeIdealTestCoverMap_chart304 R I U
    (originalMonomialTestCoverChartIndex304 I hb hn)
    (originalMonomialTestCoverChart304 I hb hn)
    (originalMonomialTestCoverChart_ideal304 I hb hn)
    (originalMonomialTestCover_scalarMap304 I hb hn) z

/-- The constructed global map preserves the original fixed base R. -/
lemma originalWholeIdealMonomialGlobalMap_toBase304 :
    originalWholeIdealMonomialGlobalMap304 R I hb hn ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  let U := localWholeQuotientMonomialAffineCover302 I hb hn
  letI : ∀ z, Algebra A (U.X z) := originalMonomialTestCoverAlgebra304 I hb hn
  letI : ∀ z, Algebra R (U.X z) := originalMonomialTestCoverFixedBaseAlgebra304 R I hb hn
  letI : ∀ z, IsScalarTower R A (U.X z) := originalMonomialTestCover_scalarTower304 R I hb hn
  exact nativeWholeIdealTestCoverMap_toBase304 R I U
    (originalMonomialTestCoverChartIndex304 I hb hn)
    (originalMonomialTestCoverChart304 I hb hn)
    (originalMonomialTestCoverChart_ideal304 I hb hn)
    (originalMonomialTestCover_scalarMap304 I hb hn)

private lemma nativeWholeIdealTestChartPresentation304
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) :
    monomialWholeIdealTestChartMap303 R i x =
      Spec.map (CommRingCat.ofHom
        ((cyclicCoefficientWholeIdealChartEquiv287 (A := A)
          i.monomials i.zeroIndex R i.zero_eq).symm x).toRingHom) ≫
        monomialCoefficientGluedChartMap300 R m n i := rfl

/-- Every original positive-degree affine test family constructs an actual global map to SAME fixed-R H.
Its patch restrictions are the original coefficient-point maps and native universal-family pullbacks.
No basis, presentation, cover or map-compatibility outcome is supplied as a premise. -/
lemma actualAffineHilbertPoint_globalFixedBaseClassifyingMap304
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
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
      ∃ g : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n,
        g ≫ monomialCoefficientGluedToBase300 R m n =
          Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        ∀ (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n),
          let S := Localization.Away i.1
          let T := Localization.Away (wholeIdealMonomialTransitionDet290
            (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
          letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
          ∃ p : UniversalCyclicCoefficientAlgebra282 R m n q.val.1 q.val.2 →ₐ[R] T,
            actualAffineHilbertPoint_monomialRestriction302 P I i q =
              cyclicCoefficientUniversalFamilyPullback302 R m n q.val.1 q.val.2 p ∧
            (localWholeQuotientMonomialAffineCover302 I hb hn).f ⟨i, q⟩ ≫ g =
              Spec.map (CommRingCat.ofHom p.toRingHom) ≫
                monomialCoefficientGluedChartMap300 R m n ⟨q.val.1, q.val.2, q.property⟩ := by
  obtain ⟨I, e, h, hb⟩ := actualAffineHilbertPoint_localWholeQuotientBases301 P
  refine ⟨I, e, hb, h, originalWholeIdealMonomialGlobalMap304 R I hb hn,
    originalWholeIdealMonomialGlobalMap_toBase304 R I hb hn, ?_⟩
  intro i q
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
  let x := wholeQuotientMonomialChart_on_cover299
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q
  let a : MonomialCoefficientChartIndex300 m n := ⟨q.val.1, q.val.2, q.property⟩
  let p : UniversalCyclicCoefficientAlgebra282 R m n q.val.1 q.val.2 →ₐ[R] T :=
    (cyclicCoefficientWholeIdealChartEquiv287 (A := T) q.val.1 q.val.2 R q.property).symm x
  refine ⟨p, ?_, ?_⟩
  · exact (actualAffineHilbertPoint_monomialRestriction_eq_chart302 P I e h i q).trans
      (monomialWholeIdealNativeFamily_isUniversalPullback302 R (A := T)
        q.val.1 q.val.2 q.property x).symm
  · exact (originalWholeIdealMonomialGlobalMap_chart304 R I hb hn ⟨i, q⟩).trans
      (nativeWholeIdealTestChartPresentation304 R (A := T) a x)

end PfaffianDescent
