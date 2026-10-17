import PfaffianDescent.OriginalNormalizedAffineClassifier317
import PfaffianDescent.OriginalNormalizedProjectiveTower317
import PfaffianDescent.NativeRelativeCartesianPointNaturality317

/-! Original-ground normalized classifiers commute with actual algebra maps.
All physical Cartesian diagrams are derived from the original projective
coefficient maps. No naturality or classifying-map equation is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R]
variable {B S : Type u} [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
variable (π : B →ₐ[R] S)

private lemma originalTestScalarComp317 :
    π.toRingHom.comp (algebraMap R B) = algebraMap R S := by
  ext x
  exact π.commutes x

def originalNormalizedAffineTestMap317 :
    originalNormalizedAffineTest317 R S ⟶ originalNormalizedAffineTest317 R B :=
  Over.homMk (Spec.map (CommRingCat.ofHom π.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom π.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R S))
    rw [← Spec.map_comp]
    exact congrArg (fun h : R →+* S => Spec.map (CommRingCat.ofHom h))
      (originalTestScalarComp317 R π))

variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4)

lemma originalNormalizedTestEquation317 :
    (p.map (algebraMap R B)).map π.toRingHom = p.map (algebraMap R S) :=
  (MvPolynomial.map_map (algebraMap R B) π.toRingHom p).trans
    (congrArg (fun h : R →+* S => p.map h) (originalTestScalarComp317 R π))

def originalNormalizedAffineTestReduction317 :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R S)) j)) ⟶
      Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)) :=
  originalNormalizedProjectiveReductionOfEquation317 π.toRingHom
    (p.map (algebraMap R B)) (hp.map (algebraMap R B))
    (p.map (algebraMap R S)) (hp.map (algebraMap R S))
    (originalNormalizedTestEquation317 R π p) j

lemma originalNormalizedAffineTestReduction_isPullback317 :
    IsPullback (originalNormalizedAffineTestReduction317 R π p hp j)
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R S)) j))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j))))
      (originalNormalizedAffineTestMap317 R π).left :=
  originalNormalizedProjectiveReductionOfEquation_isPullback317 π.toRingHom
    (p.map (algebraMap R B)) (hp.map (algebraMap R B))
    (p.map (algebraMap R S)) (hp.map (algebraMap R S))
    (originalNormalizedTestEquation317 R π p) j

lemma originalNormalizedAffineTestReduction_toOriginal317 :
    originalNormalizedAffineTestReduction317 R π p hp j ≫
        originalNormalizedProjectiveChartReduction312 (algebraMap R B) p hp j =
      originalNormalizedProjectiveChartReduction312 (algebraMap R S) p hp j := by
  have h := originalNormalizedProjectiveReductionOfEquation_comp317
    (algebraMap R B) p hp (p.map (algebraMap R B)) (hp.map (algebraMap R B)) rfl j
    π.toRingHom (p.map (algebraMap R S)) (hp.map (algebraMap R S))
    (originalNormalizedTestEquation317 R π p)
  simpa only [originalTestScalarComp317, originalNormalizedAffineTestReduction317,
    originalNormalizedProjectiveReductionOfEquation_default317] using h

def originalNormalizedAffinePointReduction317 (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R S)) j)))) n :=
  finiteFlatHilbertBaseChange195 _ _ _ _
    (originalNormalizedAffineTestReduction_isPullback317 R π p hp j) n Q

lemma originalNormalizedAffinePointReduction_wholeIdeal317 (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    (originalNormalizedAffinePointReduction317 R π p hp j n Q).val =
      Q.val.comap (originalNormalizedAffineTestReduction317 R π p hp j) := rfl

lemma originalNormalizedAffineTestPointEquiv_natural317 (n : ℕ)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    originalNormalizedAffineTestPointEquiv317 R p hp j S n
        (originalNormalizedAffinePointReduction317 R π p hp j n Q) =
      (relativeFiniteFlatHilbertFunctor197 (originalNormalizedPolynomialFamily317 R p j) n).map
        (originalNormalizedAffineTestMap317 R π).op
        (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q) :=
  nativeRelativeCartesianPointEquiv_natural317
    (originalNormalizedPolynomialFamily317 R p j) (originalNormalizedAffineTestMap317 R π)
    _ _ (originalNormalizedAffineTest_isPullback317 R p hp j S)
    _ _ (originalNormalizedAffineTest_isPullback317 R p hp j B)
    (originalNormalizedAffineTestReduction317 R π p hp j)
    (originalNormalizedAffineTestReduction_toOriginal317 R π p hp j)
    (originalNormalizedAffineTestReduction_isPullback317 R π p hp j).w
    (originalNormalizedAffineTestReduction_isPullback317 R π p hp j) n Q

lemma originalNormalizedAffineClassifyingMap_natural317 (n : ℕ) (hn : 0 < n)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    originalNormalizedAffineClassifyingMap317 R p hp j S n hn
        (originalNormalizedAffinePointReduction317 R π p hp j n Q) =
      originalNormalizedAffineTestMap317 R π ≫
        originalNormalizedAffineClassifyingMap317 R p hp j B n hn Q :=
  (congrArg
    (polynomialHypersurfaceHilbertClassificationEquiv312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn (originalNormalizedAffineTest317 R S))
    (originalNormalizedAffineTestPointEquiv_natural317 R π p hp j n Q)).trans
      (polynomialHypersurfaceHilbertClassificationEquiv_natural312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) hn (originalNormalizedAffineTestMap317 R π)
        (originalNormalizedAffineTestPointEquiv317 R p hp j B n Q))

end PfaffianDescent
end
