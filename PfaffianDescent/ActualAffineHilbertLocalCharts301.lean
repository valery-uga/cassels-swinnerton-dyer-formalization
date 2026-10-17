import PfaffianDescent.WholeQuotientFiniteFlatLocalBasis301
import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u

private lemma isoPresentation_base301
    {X Z Y T : Scheme.{u}} (e : X ≅ Z) (i : X ⟶ Y) (j : Z ⟶ Y) (f : Y ⟶ T)
    (h : i = e.hom ≫ j) : j ≫ f = e.inv ≫ (i ≫ f) := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma finiteFlatDegree_isoSource301
    {X Y T : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ T) [IsFinite g] [Flat g]
    (f : X ⟶ T) (hf : f = e.hom ≫ g) {n : ℕ} (hd : ∀ t : T, g.finrank t = n) :
    IsFinite f ∧ Flat f ∧ ∀ t : T, f.finrank t = n := by
  subst f
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro t
  exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom g) t).trans (hd t)

private lemma quotientFamily_comp301 {A : Type u} [CommRing A] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) A)) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.mk_comp_algebraMap]

variable {A : Type u} [CommRing A] {m n : ℕ}

/-- Extract the SAME whole affine quotient presentation from an actual195 ideal-sheaf point.
The presentation and finite-flat constant degree are constructed, not supplied. -/
lemma actualAffineHilbertPoint_presentation301
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n) :
    ∃ (I : Ideal (MvPolynomial (Fin m) A))
      (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I))),
      P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))) ∧
      ∀ p : PrimeSpectrum A,
        (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))).finrank p = n := by
  let F := Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))
  let G := P.val.subschemeι ≫ F
  letI : IsFinite G := P.property.1
  letI : Flat G := P.property.2.1
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff
    (R := CommRingCat.of (MvPolynomial (Fin m) A)) (f := P.val.subschemeι)).mp inferInstance
  have hb : Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I))) =
      e.inv ≫ G :=
    (quotientFamily_comp301 I).symm.trans
      (isoPresentation_base301 e P.val.subschemeι
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F hi)
  have ht := finiteFlatDegree_isoSource301 e.symm G
    (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A ⧸ I)))) hb P.property.2.2
  exact ⟨I, e, hi, ht⟩

/-- Arbitrary actual195 affine points construct local rank-n bases of the same entire ideal.
This endpoint assumes no affine presentation or quotient basis. -/
lemma actualAffineHilbertPoint_localWholeQuotientBases301
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n) :
    ∃ (I : Ideal (MvPolynomial (Fin m) A))
      (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I))),
      P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
        (Basis (Fin n) (Localization.Away s)
          (MvPolynomial (Fin m) (Localization.Away s) ⧸
            I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))) := by
  obtain ⟨I, e, hi, hfinite, hflat, hd⟩ := actualAffineHilbertPoint_presentation301 P
  letI := hfinite
  letI := hflat
  exact ⟨I, e, hi, wholeQuotientFiniteFlatDegree_localBasis301 I hd⟩

/-- Feed the internally constructed bases to299's actual covers and monomial-chart data.
The cover is the canonical determinant cover; every patch retains the extended original ideal. -/
lemma actualAffineHilbertPoint_localMonomialCharts301
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (hn : 0 < n) :
    ∃ (I : Ideal (MvPolynomial (Fin m) A))
      (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I))),
      P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal,
        ∃ b : Basis (Fin n) (Localization.Away s)
          (MvPolynomial (Fin m) (Localization.Away s) ⧸
            I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))),
        ∃ cov : (Spec (.of (Localization.Away s))).AffineOpenCover,
          cov = wholeQuotientMonomialBasisAffineCover299
            (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))) b hn ∧
          ∀ q : MonomialBasisOpenIndex299 m n,
            ∃ x : MonomialWholeIdealChart287
              (A := Localization.Away (wholeIdealMonomialTransitionDet290
                (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))) b q.val.1)) q.val.1,
              x.val = (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))).map
                (MvPolynomial.map (algebraMap (Localization.Away s)
                  (Localization.Away (wholeIdealMonomialTransitionDet290
                    (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))) b q.val.1)))) := by
  obtain ⟨I, e, hi, hb⟩ := actualAffineHilbertPoint_localWholeQuotientBases301 P
  refine ⟨I, e, hi, ?_⟩
  intro p
  obtain ⟨s, hs, ⟨b⟩⟩ := hb p
  refine ⟨s, hs, b, wholeQuotientMonomialBasisAffineCover299
    (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))) b hn, rfl, ?_⟩
  intro q
  exact ⟨wholeQuotientMonomialChart_on_cover299
    (I.map (MvPolynomial.map (algebraMap A (Localization.Away s)))) b q, rfl⟩

end PfaffianDescent
