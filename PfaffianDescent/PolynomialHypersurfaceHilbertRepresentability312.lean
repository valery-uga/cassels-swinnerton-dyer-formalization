import PfaffianDescent.MonomialRelativeLocusContainedClassification312

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- The literal hypersurface uses its ORIGINAL scalar structure over Spec R. -/
lemma monomialOriginalPolynomialHypersurfaceEmbedding_toBase312 :
    monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m =
      Spec.map (CommRingCat.ofHom (R := R)
        (S := MvPolynomial (Fin m) R ⧸ Ideal.span {p})
        (algebraMap R (MvPolynomial (Fin m) R ⧸ Ideal.span {p}))) := by
  rw [monomialOriginalPolynomialHypersurfaceEmbedding312, nativePolynomialProjection300,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Classification of GENUINE original hypersurface197 families on ALL tests.
Physical containment is supplied internally by313, then the actual locus
factor is derived by312/311. No extra outcome assumption is supplied. -/
def polynomialHypersurfaceHilbertClassificationEquiv312 (hn : 0 < n)
    (T : Over (Spec (.of R))) :
    FiniteFlatHilbertPoint195
      (relativeHilbertFamily197
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) T) n ≃
      (T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p) :=
  (relativeClosedAmbientPointEquiv313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m) n T).trans
      (monomialRelativeContainedHilbertClassificationEquiv312 R m n p hn T)

/-- Genuine NatIso represents the LITERAL original hypersurface197 functor
by the actual closed finite-coefficient-equation locus in SAME H300. -/
def polynomialHypersurfaceHilbertRepresentingIso312 (hn : 0 < n) :
    relativeFiniteFlatHilbertFunctor197
      (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) n ≅
      yoneda.obj (monomialPolynomialContainmentRepresentingObject312 R m n p) :=
  relativeClosedAmbientFiniteFlatFunctorIso313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m) n ≪≫
      monomialRelativeContainedHilbertRepresentingIso312 R m n p hn

lemma polynomialHypersurfaceHilbertRepresentingIso_inv_apply312 (hn : 0 < n)
    (T : Over (Spec (.of R)))
    (d : T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p) :
    (polynomialHypersurfaceHilbertRepresentingIso312 R m n p hn).inv.app (.op T) d =
      (polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T).symm d := rfl

/-- Entire embedded original hypersurface family recovers the literal global
universal whole ideal in the original polynomial test ambient after313 embedding. -/
lemma polynomialHypersurfaceHilbertClassificationEquiv_inv_ambientIdeal312 (hn : 0 < n)
    (T : Over (Spec (.of R)))
    (d : T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p) :
    ((polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T).symm d).val.map
        (relativeClosedAmbientTestMap313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
          (nativePolynomialProjection300 R m) T) =
      (monomialRelativeUniversalPullback309 R m n T
        (d ≫ monomialPolynomialContainmentRepresentingInclusion312 R m n p)).val :=
  relativeClosedAmbientPointEquiv_inv_ambientIdeal313
    (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
    (nativePolynomialProjection300 R m) n T
    (monomialRelativeLocusUniversalContainedPoint312 R m n p T d)

/-- ALL native original-base test morphisms preserve the hypersurface classifier. -/
lemma polynomialHypersurfaceHilbertClassificationEquiv_natural312 (hn : 0 < n)
    {T0 T1 : Over (Spec (.of R))} (a : T0 ⟶ T1)
    (Q : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) T1) n) :
    polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T0
        ((relativeFiniteFlatHilbertFunctor197
          (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) n).map
            a.op Q) =
      a ≫ polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T1 Q := by
  change monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T0
      (relativeClosedAmbientPointEquiv313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
        (nativePolynomialProjection300 R m) n T0
        ((relativeFiniteFlatHilbertFunctor197
          (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) n).map
            a.op Q)) = _
  rw [relativeClosedAmbientPointEquiv_natural313]
  exact monomialRelativeContainedHilbertClassifyingMap_natural312 R m n p hn a _

/-- A GENUINE original hypersurface family constructs a unique map to the
actual locus with only the original point and hn. Its ambient embedding,
finite-flat properties, original polynomial and whole ideal are preserved. -/
theorem originalRelativePolynomialHypersurfacePoint_existsUnique_classifyingMap312
    (hn : 0 < n) (T : Over (Spec (.of R)))
    (Q : FiniteFlatHilbertPoint195
      (relativeHilbertFamily197
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p ≫ nativePolynomialProjection300 R m) T) n) :
    ∃! d : T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p,
      Q = (polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T).symm d := by
  let e := polynomialHypersurfaceHilbertClassificationEquiv312 R m n p hn T
  refine ⟨e Q, (e.symm_apply_apply Q).symm, ?_⟩
  intro d hd
  exact (e.apply_symm_apply d).symm.trans (congrArg e hd.symm)

end PfaffianDescent
end
