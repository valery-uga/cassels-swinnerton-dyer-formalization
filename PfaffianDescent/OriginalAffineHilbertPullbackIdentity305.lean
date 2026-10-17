import PfaffianDescent.NativeFixedBaseUniversalFamilyPullback305
import PfaffianDescent.NativePolynomialTestCoverUniqueness305
import PfaffianDescent.OriginalAffineHilbertGlobalMap304

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

/-- Literal composed polynomial Spec map, formed before original localization substitution. -/
lemma twoStagePolynomialTestSpecMap305
    {A S T : Type u} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra S T] (m : ℕ) :
    letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A S))) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A T))) := by
  letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
  have h : (MvPolynomial.map (σ := Fin m) (algebraMap S T)).comp
      (MvPolynomial.map (σ := Fin m) (algebraMap A S)) =
      MvPolynomial.map (σ := Fin m) (algebraMap A T) :=
    RingHom.ext (MvPolynomial.map_map (algebraMap A S) (algebraMap S T))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The original two-stage195 restriction has the same native whole ideal as the composed ambient map. -/
lemma actualAffineHilbertPoint_monomialRestriction_composedIdeal305
    {A : Type u} [CommRing A] {m n : ℕ}
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    let S := Localization.Away i.1
    let T := Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
    letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
    (actualAffineHilbertPoint_monomialRestriction302 P I i q).val =
      P.val.comap (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A T)))) :=
by
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  letI : Algebra A T := twoStageTestCoefficientAlgebra304 A S T
  exact (actualAffineHilbertPoint_monomialRestriction_ideal302 P I i q).trans
    (congrArg P.val.comap (twoStagePolynomialTestSpecMap305 (A := A) (S := S) (T := T) m))

section OriginalCoverActions
variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A))
variable (hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
  (Basis (Fin n) (Localization.Away s)
    (MvPolynomial (Fin m) (Localization.Away s) ⧸
      I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))))) (hn : 0 < n)

/-- Construct the fixed-R coefficient hom at abstract ring dictionaries,
without asking instance search for scalar actions on concrete localizations. -/
private def originalTwoStageFixedBaseAlgHom305
    (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra A S] [Algebra S T] :
    letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
    A →ₐ[R] T := by
  letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
  exact { (algebraMap S T).comp (algebraMap A S) with commutes' := fun _ => rfl }

private def originalPullbackTestCoverAlgebra305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  twoStageTestCoefficientAlgebra304 A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

private def originalPullbackTestCoverFixedBaseAlgebra305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  fixedBaseCompositePatchAlgebra302 R A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

/-- The actual cover's coefficient hom keeps its original composed ring map. -/
private def originalPullbackTestCoverAlgHom305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverFixedBaseAlgebra305 R I hb hn z
    A →ₐ[R] ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  originalTwoStageFixedBaseAlgHom305 R A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

private lemma originalPullbackTestCoverAlgHom_toRingHom305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverAlgebra305 I hb hn z
    letI : Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverFixedBaseAlgebra305 R I hb hn z
    (originalPullbackTestCoverAlgHom305 R I hb hn z).toRingHom =
      algebraMap A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) := rfl

private lemma originalPullbackTestCover_scalarTower305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverAlgebra305 I hb hn z
    letI : Algebra R ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverFixedBaseAlgebra305 R I hb hn z
    IsScalarTower R A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
  twoStageTestCoefficient_scalarTower304 R A (Localization.Away z.1.1)
    (Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A (Localization.Away z.1.1)))) z.1.2 z.2.val.1))

private lemma originalPullbackTestCover_scalarMap305
    (z : (localWholeQuotientMonomialAffineCover302 I hb hn).I₀) :
    letI : Algebra A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z) :=
      originalPullbackTestCoverAlgebra305 I hb hn z
    (localWholeQuotientMonomialAffineCover302 I hb hn).f z =
      Spec.map (CommRingCat.ofHom (algebraMap A ((localWholeQuotientMonomialAffineCover302 I hb hn).X z))) :=
  twoStageTestCoefficientSpecMap304
end OriginalCoverActions

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original positive-degree affine test point is the ACTUAL pullback of the constructed SAME-H
universal family along an internally constructed fixed-R morphism. Equality is of whole native ideals. -/
lemma actualAffineHilbertPoint_isGlobalUniversalPullback305
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) (hn : 0 < n) :
    ∃ g : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n,
      ∃ hg : g ≫ monomialCoefficientGluedToBase300 R m n =
        Spec.map (CommRingCat.ofHom (algebraMap R A)),
      P = fixedBaseUniversalFamilyPullback305 R m n g hg := by
  obtain ⟨I, e, hb, h, g, hg, hpatch⟩ := actualAffineHilbertPoint_globalFixedBaseClassifyingMap304 R P hn
  let U := localWholeQuotientMonomialAffineCover302 I hb hn
  letI : ∀ z, Algebra A (U.X z) := originalPullbackTestCoverAlgebra305 I hb hn
  letI : ∀ z, Algebra R (U.X z) := originalPullbackTestCoverFixedBaseAlgebra305 R I hb hn
  have hf : ∀ z, U.f z = Spec.map (CommRingCat.ofHom (algebraMap A (U.X z))) :=
    originalPullbackTestCover_scalarMap305 I hb hn
  refine ⟨g, hg, ?_⟩
  apply nativeAffineHilbertPoint_eq_of_polynomialTestCover305 m U hf
  intro z
  let f : A →ₐ[R] (U.X z) := originalPullbackTestCoverAlgHom305 R I hb hn z
  have hfRing : f.toRingHom = algebraMap A (U.X z) :=
    originalPullbackTestCoverAlgHom_toRingHom305 R I hb hn z
  let a : MonomialCoefficientChartIndex300 m n :=
    originalMonomialTestCoverChartIndex304 I hb hn z
  obtain ⟨p0, hp, hm⟩ := hpatch z.1 z.2
  let p : UniversalCyclicCoefficientAlgebra282 R m n a.monomials a.zeroIndex →ₐ[R] (U.X z) := p0
  have hm' : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ monomialCoefficientGluedChartMap300 R m n a :=
    by
      rw [hfRing]
      exact (congrArg (fun k => k ≫ g) (hf z).symm).trans hm
  have hchart := fixedBaseUniversalFamilyPullback_chartIdeal305 R m n g hg a f p hm'
  rw [hfRing] at hchart
  exact (actualAffineHilbertPoint_monomialRestriction_composedIdeal305 P I z.1 z.2).symm.trans
    ((congrArg Subtype.val hp).trans hchart.symm)

end PfaffianDescent
