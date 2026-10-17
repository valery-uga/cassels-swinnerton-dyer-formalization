import PfaffianDescent.OriginalNormalizedHypersurfaceAffineChart312
import AllCharacteristics.PolynomialQuotientBaseChange

/-! SOURCE ONLY312. Actual native base change of the explicitly normalized
original hypersurface polynomial. Every Cartesian square and relative test
ambient isomorphism is derived from the original polynomial quotient, with
no supplied chart compatibility, representation or lifting conclusion. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

private def normalizedQuotientEqSpecIso312
    {S : Type u} [CommRing S] {m : ℕ}
    (I J : Ideal (MvPolynomial (Fin m) S)) (h : I = J) :
    Spec (.of (MvPolynomial (Fin m) S ⧸ J)) ≅
      Spec (.of (MvPolynomial (Fin m) S ⧸ I)) :=
  Scheme.Spec.mapIso (Ideal.quotEquivOfEq h).toCommRingCatIso.op

private lemma normalizedQuotientEqSpecIso_toBase312
    {S : Type u} [CommRing S] {m : ℕ}
    (I J : Ideal (MvPolynomial (Fin m) S)) (h : I = J) :
    (normalizedQuotientEqSpecIso312 I J h).hom ≫
        Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.baseMap I)) =
      Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.baseMap J)) := by
  change Spec.map (CommRingCat.ofHom (Ideal.quotEquivOfEq h).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.baseMap I)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

private def normalizedPolynomialQuotientReduction312
    {R S : Type u} [CommRing R] [CommRing S] {m : ℕ}
    (b : R →+* S) (I : Ideal (MvPolynomial (Fin m) R))
    (J : Ideal (MvPolynomial (Fin m) S)) (h : I.map (MvPolynomial.map b) = J) :
    Spec (.of (MvPolynomial (Fin m) S ⧸ J)) ⟶
      Spec (.of (MvPolynomial (Fin m) R ⧸ I)) :=
  (normalizedQuotientEqSpecIso312 (I.map (MvPolynomial.map b)) J h).hom ≫
    Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.coefficientMap b I))

private lemma normalizedPolynomialQuotientReduction_isPullback312
    {R S : Type u} [CommRing R] [CommRing S] {m : ℕ}
    (b : R →+* S) (I : Ideal (MvPolynomial (Fin m) R))
    (J : Ideal (MvPolynomial (Fin m) S)) (h : I.map (MvPolynomial.map b) = J) :
    IsPullback (normalizedPolynomialQuotientReduction312 b I J h)
      (Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.baseMap J)))
      (Spec.map (CommRingCat.ofHom (AllCharacteristics.PolynomialQuotient.baseMap I)))
      (Spec.map (CommRingCat.ofHom b)) := by
  apply (AllCharacteristics.PolynomialQuotient.isPullback_spec b I).of_iso'
    (normalizedQuotientEqSpecIso312 (I.map (MvPolynomial.map b)) J h)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · exact (normalizedQuotientEqSpecIso_toBase312
      (I.map (MvPolynomial.map b)) J h).trans (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

variable {R S : Type u} [CommRing R] [CommRing S]
variable (b : R →+* S) (p : MvPolynomial (Fin 4) R) (j : Fin 4)

/-- Entire original normalized equation ideal, with nilpotents retained. -/
lemma originalNormalizedHypersurfaceIdeal_map312 :
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 p j}).map (MvPolynomial.map b) =
      Ideal.span {originalNormalizedHypersurfacePolynomial312 (p.map b) j} := by
  rw [Ideal.map_span, Set.image_singleton, originalNormalizedHypersurfacePolynomial_map312]

/-- Original coefficient quotient produces the actual polynomial test map. -/
def originalNormalizedHypersurfaceReduction312 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j)) ⟶
      Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) :=
  normalizedPolynomialQuotientReduction312 b
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 p j})
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 (p.map b) j})
    (originalNormalizedHypersurfaceIdeal_map312 b p j)

/-- The normalized original hypersurface's physical coefficient change is
genuinely Cartesian over the original scalar maps. -/
lemma originalNormalizedHypersurfaceReduction_isPullback312 :
    IsPullback (originalNormalizedHypersurfaceReduction312 b p j)
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))))
      (Spec.map (CommRingCat.ofHom b)) :=
  normalizedPolynomialQuotientReduction_isPullback312 b
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 p j})
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 (p.map b) j})
    (originalNormalizedHypersurfaceIdeal_map312 b p j)

lemma originalNormalizedHypersurfaceReduction_toBase312 :
    originalNormalizedHypersurfaceReduction312 b p j ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) =
      Spec.map (CommRingCat.ofHom
          (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))) ≫
        Spec.map (CommRingCat.ofHom b) :=
  (originalNormalizedHypersurfaceReduction_isPullback312 b p j).w

/-- Actual normalized quotient is the literal arbitrary-test affine ambient,
via the DERIVED Cartesian square, not a supplied presentation isomorphism. -/
def originalNormalizedHypersurfaceRelativeAmbientIso312 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j)) ≅
      pullback (Spec.map (CommRingCat.ofHom b))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j)))) :=
  (originalNormalizedHypersurfaceReduction_isPullback312 b p j).flip.isoPullback

lemma originalNormalizedHypersurfaceRelativeAmbientIso_toTest312 :
    (originalNormalizedHypersurfaceRelativeAmbientIso312 b p j).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom b))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map b) j))) :=
  (originalNormalizedHypersurfaceReduction_isPullback312 b p j).flip.isoPullback_hom_fst

lemma originalNormalizedHypersurfaceRelativeAmbientIso_toOriginal312 :
    (originalNormalizedHypersurfaceRelativeAmbientIso312 b p j).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom b))
          (Spec.map (CommRingCat.ofHom
            (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j)))) =
      originalNormalizedHypersurfaceReduction312 b p j :=
  (originalNormalizedHypersurfaceReduction_isPullback312 b p j).flip.isoPullback_hom_snd

end PfaffianDescent
end
