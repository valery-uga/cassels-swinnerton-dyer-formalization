import PfaffianDescent.NativeFiniteFlatAmbientIsoTransport317
import PfaffianDescent.OriginalNormalizedProjectiveReduction312
import PfaffianDescent.PolynomialHypersurfaceHilbertRepresentability312

/-! SOURCE ONLY317. A genuine whole family in the physical normalized chart
over a test ring constructs a classifier into the SAME original-ground
polynomial locus. The relative ambient and point equivalence are DERIVED.
No representation, chart compatibility or classifier outcome is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (p : MvPolynomial (Fin 4) R) {d : ℕ}
variable (hp : p.IsHomogeneous d) (j : Fin 4)

def originalNormalizedPolynomialFamily317 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) ⟶ Spec (.of R) :=
  monomialOriginalPolynomialHypersurfaceEmbedding312 R 3
      (originalNormalizedHypersurfacePolynomial312 p j) ≫ nativePolynomialProjection300 R 3

lemma originalNormalizedPolynomialFamily_toBase317 :
    originalNormalizedPolynomialFamily317 R p j =
      Spec.map (CommRingCat.ofHom (R := R)
        (S := OriginalNormalizedHypersurfaceAlgebra312 p j)
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) :=
  monomialOriginalPolynomialHypersurfaceEmbedding_toBase312 R 3
    (originalNormalizedHypersurfacePolynomial312 p j)

variable (B : Type u) [CommRing B] [Algebra R B]

def originalNormalizedAffineTest317 : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))

private lemma nativePullbackProjectionEq317 {X0 X B0 B1 : Scheme.{u}}
    (a : X0 ⟶ X) (F0 : X0 ⟶ B0) (F G : X ⟶ B1) (b : B0 ⟶ B1)
    (h : F = G) (H : IsPullback a F0 G b) : IsPullback a F0 F b := by
  cases h
  exact H

lemma originalNormalizedAffineTest_isPullback317 :
    IsPullback (originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j)
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j))))
      (originalNormalizedPolynomialFamily317 R p j)
      (originalNormalizedAffineTest317 R B).hom :=
  nativePullbackProjectionEq317 _ _ _ _ _
    (originalNormalizedPolynomialFamily_toBase317 R p j)
    (originalNormalizedProjectiveChartReduction_isPullback312 (algebraMap R B) p hp j)

/-- The actual normalized projective chart is the literal original polynomial
relative ambient over Spec B, with all structure maps retained. -/
def originalNormalizedAffineTestAmbientIso317 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)) ≅
      pullback (originalNormalizedAffineTest317 R B).hom
        (originalNormalizedPolynomialFamily317 R p j) :=
  (originalNormalizedAffineTest_isPullback317 R p hp j B).flip.isoPullback

lemma originalNormalizedAffineTestAmbientIso_toTest317 :
    (originalNormalizedAffineTestAmbientIso317 R p hp j B).hom ≫
        relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j)
          (originalNormalizedAffineTest317 R B) =
      Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j))) :=
  (originalNormalizedAffineTest_isPullback317 R p hp j B).flip.isoPullback_hom_fst

/-- This equivalence uses a physical chart195 point, not a supplied relative
point or desired classifier. Its Cartesian ambient was constructed above. -/
def originalNormalizedAffineTestPointEquiv317 (n : ℕ) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n ≃
      FiniteFlatHilbertPoint195
        (relativeHilbertFamily197 (originalNormalizedPolynomialFamily317 R p j)
          (originalNormalizedAffineTest317 R B)) n :=
  nativeFiniteFlatPointAmbientIsoEquiv317 _ _
    (originalNormalizedAffineTestAmbientIso317 R p hp j B)
    (originalNormalizedAffineTestAmbientIso_toTest317 R p hp j B) n

lemma originalNormalizedAffineTestPointEquiv_wholeIdeal317 (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q).val =
      Q.val.comap (originalNormalizedAffineTestAmbientIso317 R p hp j B).inv := rfl

/-- Actual map to SAME original-ground locus, formed from the genuine whole
normalized family. The parameter base stays original R. -/
def originalNormalizedAffineClassifyingMap317 (n : ℕ) (hn : 0 < n)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    originalNormalizedAffineTest317 R B ⟶ monomialPolynomialContainmentRepresentingObject312
      R 3 n (originalNormalizedHypersurfacePolynomial312 p j) :=
  polynomialHypersurfaceHilbertClassificationEquiv312 R 3 n
    (originalNormalizedHypersurfacePolynomial312 p j) hn
    (originalNormalizedAffineTest317 R B)
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q)

/-- Pulling the original representing family back along that classifier and
returning through the actual chart equivalence recovers the entire input. -/
lemma originalNormalizedAffineClassifyingMap_recoversPoint317 (n : ℕ) (hn : 0 < n)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n).symm
      ((polynomialHypersurfaceHilbertClassificationEquiv312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) hn
        (originalNormalizedAffineTest317 R B)).symm
        (originalNormalizedAffineClassifyingMap317 R p hp j B n hn Q)) = Q := by
  exact (congrArg (originalNormalizedAffineTestPointEquiv317 R p hp j B n).symm
    ((polynomialHypersurfaceHilbertClassificationEquiv312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn
      (originalNormalizedAffineTest317 R B)).symm_apply_apply
        (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q))).trans
          ((originalNormalizedAffineTestPointEquiv317 R p hp j B n).symm_apply_apply Q)

end PfaffianDescent
end
