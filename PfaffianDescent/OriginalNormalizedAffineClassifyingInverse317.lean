import PfaffianDescent.OriginalNormalizedClassifierNaturality317

/-! Physical normalized families recovered from maps to the original-ground
representing locus, with exact compatibility under every scalar reduction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (p : MvPolynomial (Fin 4) R) {d : ℕ}
  (hp : p.IsHomogeneous d) (j : Fin 4) (B : Type u) [CommRing B] [Algebra R B]
  (n : ℕ) (hn : 0 < n)

def originalNormalizedAffineClassifierEquiv317 :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n ≃
    (originalNormalizedAffineTest317 R B ⟶ monomialPolynomialContainmentRepresentingObject312
      R 3 n (originalNormalizedHypersurfacePolynomial312 p j)) :=
  (originalNormalizedAffineTestPointEquiv317 R p hp j B n).trans
    (polynomialHypersurfaceHilbertClassificationEquiv312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn
      (originalNormalizedAffineTest317 R B))

def originalNormalizedAffinePointOfClassifier317
    (c : originalNormalizedAffineTest317 R B ⟶ monomialPolynomialContainmentRepresentingObject312
      R 3 n (originalNormalizedHypersurfacePolynomial312 p j)) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n :=
  (originalNormalizedAffineClassifierEquiv317 R p hp j B n hn).symm c

lemma originalNormalizedAffinePointOfClassifier_classifies317
    (c : originalNormalizedAffineTest317 R B ⟶ monomialPolynomialContainmentRepresentingObject312
      R 3 n (originalNormalizedHypersurfacePolynomial312 p j)) :
    originalNormalizedAffineClassifyingMap317 R p hp j B n hn
      (originalNormalizedAffinePointOfClassifier317 R p hp j B n hn c) = c :=
  (originalNormalizedAffineClassifierEquiv317 R p hp j B n hn).apply_symm_apply c

lemma originalNormalizedAffineClassifier_injective317 :
    Function.Injective (originalNormalizedAffineClassifyingMap317 R p hp j B n hn) :=
  (originalNormalizedAffineClassifierEquiv317 R p hp j B n hn).injective

variable {B} {S : Type u} [CommRing S] [Algebra R S]

lemma originalNormalizedAffinePointOfClassifier_natural317 (pi : B →ₐ[R] S)
    (c : originalNormalizedAffineTest317 R B ⟶ monomialPolynomialContainmentRepresentingObject312
      R 3 n (originalNormalizedHypersurfacePolynomial312 p j)) :
    originalNormalizedAffinePointReduction317 R pi p hp j n
      (originalNormalizedAffinePointOfClassifier317 R p hp j B n hn c) =
    originalNormalizedAffinePointOfClassifier317 R p hp j S n hn
      (originalNormalizedAffineTestMap317 R pi ≫ c) := by
  apply originalNormalizedAffineClassifier_injective317 R p hp j S n hn
  rw [originalNormalizedAffineClassifyingMap_natural317,
    originalNormalizedAffinePointOfClassifier_classifies317,
    originalNormalizedAffinePointOfClassifier_classifies317]

end PfaffianDescent
end
