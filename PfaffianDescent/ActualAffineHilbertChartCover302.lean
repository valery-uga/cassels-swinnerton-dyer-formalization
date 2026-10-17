import PfaffianDescent.LocalWholeQuotientMonomialCover302
import PfaffianDescent.NativeWholeIdealChartFamily302

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
variable {A : Type u} [CommRing A] {m n : ℕ}

/-- The literal two-stage195 restriction to a local basis patch and a determinant patch. -/
def actualAffineHilbertPoint_monomialRestriction302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    let S := Localization.Away i.1
    let T := Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := T) (S := MvPolynomial (Fin m) T)
      (@algebraMap T (MvPolynomial (Fin m) T)
      (@CommRing.toCommSemiring T (inferInstance : CommRing T))
      (@CommRing.toCommSemiring (MvPolynomial (Fin m) T) (inferInstance : CommRing (MvPolynomial (Fin m) T))).toSemiring
      inferInstance))) n := by
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  let PS := finiteFlatHilbertBaseChange195
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A S))))
    (Spec.map (CommRingCat.ofHom (R := S) (S := MvPolynomial (Fin m) S)
      (@algebraMap S (MvPolynomial (Fin m) S)
      (@CommRing.toCommSemiring S (inferInstance : CommRing S))
      (@CommRing.toCommSemiring (MvPolynomial (Fin m) S) (inferInstance : CommRing (MvPolynomial (Fin m) S))).toSemiring
      inferInstance)))
    (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A))))
    (Spec.map (CommRingCat.ofHom (R := A) (S := S)
      (@algebraMap A (S)
      (@CommRing.toCommSemiring A (inferInstance : CommRing A))
      (@CommRing.toCommSemiring (S) (inferInstance : CommRing (S))).toSemiring
      inferInstance)))
    (ambientPolynomialScalar_isCartesian296 (C := A) (S := S) (m := m)) n P
  exact finiteFlatHilbertBaseChange195
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))))
    (Spec.map (CommRingCat.ofHom (R := T) (S := MvPolynomial (Fin m) T)
      (@algebraMap T (MvPolynomial (Fin m) T)
      (@CommRing.toCommSemiring T (inferInstance : CommRing T))
      (@CommRing.toCommSemiring (MvPolynomial (Fin m) T) (inferInstance : CommRing (MvPolynomial (Fin m) T))).toSemiring
      inferInstance)))
    (Spec.map (CommRingCat.ofHom (R := S) (S := MvPolynomial (Fin m) S)
      (@algebraMap S (MvPolynomial (Fin m) S)
      (@CommRing.toCommSemiring S (inferInstance : CommRing S))
      (@CommRing.toCommSemiring (MvPolynomial (Fin m) S) (inferInstance : CommRing (MvPolynomial (Fin m) S))).toSemiring
      inferInstance)))
    (Spec.map (CommRingCat.ofHom (R := S) (S := T)
      (@algebraMap S (T)
      (@CommRing.toCommSemiring S (inferInstance : CommRing S))
      (@CommRing.toCommSemiring (T) (inferInstance : CommRing (T))).toSemiring
      inferInstance)))
    (ambientPolynomialScalar_isCartesian296 (C := S) (S := T) (m := m)) n PS

/-- The restriction's underlying ideal is exactly pullback along the patch's ambient map. -/
lemma actualAffineHilbertPoint_monomialRestriction_ideal302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    let S := Localization.Away i.1
    let T := Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
    (actualAffineHilbertPoint_monomialRestriction302 P I i q).val = P.val.comap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A S)))) :=
  (P.val.comap_comp _ _).symm

/-- Work with entire ideal sheaves before any local basis/determinant is substituted. -/
private lemma affineWholeIdealKernel_comap_twice302
    {C S T : Type u} [CommRing C] [CommRing S] [CommRing T]
    [Algebra C S] [Algebra S T] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) C)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S)))) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((I.map (MvPolynomial.map (algebraMap C S))).map
          (MvPolynomial.map (algebraMap S T)))))).ker := by
  exact ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap_comp _ _).trans
    ((congrArg
      (fun J : (Spec (.of (MvPolynomial (Fin m) S))).IdealSheafData =>
        J.comap (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T)))))
      (wholeIdealEmbeddedScalar_kernel_comap296 (C := C) (S := S) I)).trans
      (wholeIdealEmbeddedScalar_kernel_comap296 (C := S) (S := T)
        (I.map (MvPolynomial.map (algebraMap C S)))))

/-- Use the native original presentation once, without constructing or unfolding a195 pullback. -/
private lemma actualAffinePoint_comap_twice302
    {C S T : Type u} [CommRing C] [CommRing S] [CommRing T]
    [Algebra C S] [Algebra S T] {m n : ℕ}
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C)))) n)
    (I : Ideal (MvPolynomial (Fin m) C))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) C ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    P.val.comap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S)))) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((I.map (MvPolynomial.map (algebraMap C S))).map
          (MvPolynomial.map (algebraMap S T)))))).ker :=
  (congrArg
    (fun J : (Spec (.of (MvPolynomial (Fin m) C))).IdealSheafData => J.comap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap S T))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S)))))
    (actualAffineHilbertPoint_kernel_of_presentation302 P I e h)).trans
    (affineWholeIdealKernel_comap_twice302 (C := C) (S := S) (T := T) I)

/-- Assemble the canonical quotient embedding kernel at abstract coefficient/ring dictionaries. -/
private def nativePolynomialQuotientKernel302
    {C : Type u} [CommRing C] {m : ℕ} (I : Ideal (MvPolynomial (Fin m) C)) :
    (Spec (.of (MvPolynomial (Fin m) C))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom
    (R := MvPolynomial (Fin m) C) (S := MvPolynomial (Fin m) C ⧸ I)
    (@Ideal.Quotient.mk (MvPolynomial (Fin m) C)
      (inferInstance : CommRing (MvPolynomial (Fin m) C)).toRing I
      (inferInstance : I.IsTwoSided)))).ker

/-- Expose the actual chart family's whole embedding kernel before substituting originalI/localb. -/
private lemma monomialCoverNativeFamily_kernel302
    {C : Type u} [CommRing C] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin m) C))
    (b : Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I))
    (q : MonomialBasisOpenIndex299 m n) :
    (monomialWholeIdealNativeFamily302 q.val.1
      (wholeQuotientMonomialChart_on_cover299 I b q)).val =
      nativePolynomialQuotientKernel302
        (C := Localization.Away (wholeIdealMonomialTransitionDet290 I b q.val.1))
        (I.map (MvPolynomial.map (algebraMap C
          (Localization.Away (wholeIdealMonomialTransitionDet290 I b q.val.1))))) := rfl

/-- The native restricted195 point is the actual chart's whole embedded quotient family. -/
lemma actualAffineHilbertPoint_monomialRestriction_eq_chart302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    actualAffineHilbertPoint_monomialRestriction302 P I i q =
      monomialWholeIdealNativeFamily302 q.val.1
        (wholeQuotientMonomialChart_on_cover299
          (I.map (MvPolynomial.map (algebraMap A (Localization.Away i.1)))) i.2 q) := by
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  have hi := actualAffinePoint_comap_twice302
    (C := A) (S := S) (T := T) (m := m) (n := n) P I e h
  have hc := monomialCoverNativeFamily_kernel302 (C := S) (m := m) (n := n)
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q
  apply Subtype.ext
  exact (actualAffineHilbertPoint_monomialRestriction_ideal302 P I i q).trans
    (hi.trans hc.symm)

/-- Construct the coefficient map which identifies each native restriction with universal289. -/
lemma actualAffineHilbertPoint_monomialRestriction_isUniversal302
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n) :
    let S := Localization.Away i.1
    let T := Localization.Away (wholeIdealMonomialTransitionDet290
      (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
    letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
    ∃ p : UniversalCyclicCoefficientAlgebra282 A m n q.val.1 q.val.2 →ₐ[A] T,
      actualAffineHilbertPoint_monomialRestriction302 P I i q =
        cyclicCoefficientUniversalFamilyPullback302 A m n q.val.1 q.val.2 p := by
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  let x := wholeQuotientMonomialChart_on_cover299
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q
  refine ⟨(cyclicCoefficientWholeIdealChartEquiv287 (A := T) q.val.1 q.val.2 A q.property).symm x, ?_⟩
  exact (actualAffineHilbertPoint_monomialRestriction_eq_chart302 P I e h i q).trans
    (monomialWholeIdealNativeFamily_isUniversalPullback302 A (A := T)
      q.val.1 q.val.2 q.property x).symm

/-- Actual195 affine points construct an explicit affine base cover with universal289 on every patch.
No presentation, local basis, or covering conclusion is supplied as a premise. -/
lemma actualAffineHilbertPoint_universalMonomialAffineCover302
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
          letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
          ∃ p : UniversalCyclicCoefficientAlgebra282 A m n q.val.1 q.val.2 →ₐ[A] T,
            actualAffineHilbertPoint_monomialRestriction302 P I i q =
              cyclicCoefficientUniversalFamilyPullback302 A m n q.val.1 q.val.2 p := by
  obtain ⟨I, e, h, hb⟩ := actualAffineHilbertPoint_localWholeQuotientBases301 P
  exact ⟨I, e, hb, h, localWholeQuotientMonomialAffineCover302 I hb hn, rfl,
    actualAffineHilbertPoint_monomialRestriction_isUniversal302 P I e h⟩

end PfaffianDescent
