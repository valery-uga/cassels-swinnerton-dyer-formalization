import PfaffianDescent.OriginalNormalizedAffineClassifyingInverse317
import PfaffianDescent.MonomialPolynomialLocusFinitePresentation312

/-! Canonical coefficient algebra tests produce actual normalized geometric
families; reduction is equality of whole ideals, including nilpotents. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)
  (i : MonomialCoefficientChartIndex300 m n)
  {B S : Type u} [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]

def originalCoefficientTestClassifyingMap317
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] B) :
    originalNormalizedAffineTest317 R B ⟶
      monomialPolynomialContainmentRepresentingObject312 R m n p :=
  Over.homMk (Spec.map (CommRingCat.ofHom q.toRingHom) ≫
    monomialClosedCoefficientChartToLocus312 R m n p i) (by
      have hscalar : q.toRingHom.comp (algebraMap R
          (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) =
          algebraMap R B := by
        ext r
        exact q.commutes r
      have hspec : Spec.map (CommRingCat.ofHom q.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R
            (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) =
          Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
        rw [← Spec.map_comp]
        exact congrArg (fun h : R →+* B => Spec.map (CommRingCat.ofHom h)) hscalar
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun h : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
              Spec (.of R) => Spec.map (CommRingCat.ofHom q.toRingHom) ≫ h)
          (monomialPolynomialContainmentChart_toBase312 R m n p i)).trans hspec))

lemma originalCoefficientTestClassifyingMap_natural317
    (pi : B →ₐ[R] S)
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] B) :
    originalNormalizedAffineTestMap317 R pi ≫ originalCoefficientTestClassifyingMap317 R m n p i q =
      originalCoefficientTestClassifyingMap317 R m n p i (pi.comp q) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom pi.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ monomialClosedCoefficientChartToLocus312 R m n p i) =
      Spec.map (CommRingCat.ofHom (pi.comp q).toRingHom) ≫ monomialClosedCoefficientChartToLocus312 R m n p i
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
  (j : Fin 4) (hn : 0 < n)
  (k : MonomialCoefficientChartIndex300 3 n)

def originalCoefficientTestPhysicalFamily317
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) k →ₐ[R] B) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R B)) j)))) n :=
  originalNormalizedAffinePointOfClassifier317 R r hr j B n hn
    (originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) k q)

lemma originalCoefficientTestPhysicalFamily_natural317 (pi : B →ₐ[R] S)
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) k →ₐ[R] B) :
    originalNormalizedAffinePointReduction317 R pi r hr j n
      (originalCoefficientTestPhysicalFamily317 R n r hr j hn k q) =
      originalCoefficientTestPhysicalFamily317 R n r hr j hn k (pi.comp q) := by
  unfold originalCoefficientTestPhysicalFamily317
  rw [originalNormalizedAffinePointOfClassifier_natural317,
    originalCoefficientTestClassifyingMap_natural317]

lemma originalCoefficientTestPhysicalFamily_wholeIdeal317 (pi : B →ₐ[R] S)
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) k →ₐ[R] B) :
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn k q).val.comap
        (originalNormalizedAffineTestReduction317 R pi r hr j) =
      (originalCoefficientTestPhysicalFamily317 R n r hr j hn k (pi.comp q)).val :=
  (originalNormalizedAffinePointReduction_wholeIdeal317 R pi r hr j n _).symm.trans
    (congrArg Subtype.val (originalCoefficientTestPhysicalFamily_natural317 R n r hr j hn k pi q))

end PfaffianDescent
end
