import PfaffianDescent.OriginalCoefficientChartTestFamily317
import PfaffianDescent.NativeCommonAffineChartCover306

/-! Actual field-valued classifiers factor through a coefficient chart.
The chart and its algebra map are constructed, not extra assumptions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

lemma nativeFieldMapToOpenChart_algHom317
    (R : Type u) [CommRing R] {A K : Type u} [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (c : Spec (.of K) ⟶ X)
    (hc : c ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hpoint : c (IsLocalRing.closedPoint K) ∈ Set.range j) :
    ∃ q : A →ₐ[R] K, Spec.map (CommRingCat.ofHom q.toRingHom) ≫ j = c := by
  have hrange : Set.range c ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hx]
    exact hpoint
  let a := IsOpenImmersion.lift j c hrange
  have ha : a ≫ j = c := IsOpenImmersion.lift_fac j c hrange
  have hbase : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
    (congrArg (fun f => a ≫ f) hj.symm).trans
      ((Category.assoc a j F).symm.trans ((congrArg (fun f => f ≫ F) ha).trans hc))
  obtain ⟨q, hq⟩ := nativeAffineMapOverBase_algHom_exists306 R a hbase
  exact ⟨q, (congrArg (fun f => f ≫ j) hq).trans ha⟩

lemma originalFieldClassifier_coefficientChart_exists317
    (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (K : Type u) [Field K] [Algebra R K]
    (c : originalNormalizedAffineTest317 R K ⟶
      monomialPolynomialContainmentRepresentingObject312 R m n p) :
    ∃ (i : MonomialCoefficientChartIndex300 m n)
      (q : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] K),
      originalCoefficientTestClassifyingMap317 R m n p i q = c := by
  let C := monomialClosedCoefficientLocusOpenCover312 R m n p
  let x := c.left (IsLocalRing.closedPoint K)
  let i : MonomialCoefficientChartIndex300 m n := (C.idx x).down
  have hi : C.f (C.idx x) = monomialClosedCoefficientChartToLocus312 R m n p i :=
    monomialClosedCoefficientLocusOpenCover_map312 R m n p i
  have hpoint : x ∈ Set.range (monomialClosedCoefficientChartToLocus312 R m n p i) :=
    Eq.mp (congrArg (fun f : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
      monomialPolynomialContainmentLocus310 R m n p => x ∈ Set.range f) hi) (C.covers x)
  have hopen : IsOpenImmersion (monomialClosedCoefficientChartToLocus312 R m n p i) :=
    Eq.mp (congrArg (fun f => IsOpenImmersion f) hi) (C.map_prop (C.idx x))
  obtain ⟨q, hq⟩ := @nativeFieldMapToOpenChart_algHom317 R _
    (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) K _ _ _ _
    (monomialPolynomialContainmentLocus310 R m n p)
    (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
    (monomialClosedCoefficientChartToLocus312 R m n p i) hopen
    (monomialPolynomialContainmentChart_toBase312 R m n p i) c.left c.w hpoint
  refine ⟨i, q, ?_⟩
  apply Over.OverMorphism.ext
  exact hq

lemma originalFieldPhysicalFamily_coefficientChart_exists317
    (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R) {d : ℕ}
    (hr : r.IsHomogeneous d) (j : Fin 4) (K : Type u) [Field K] [Algebra R K]
    (n : ℕ) (hn : 0 < n)
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := K)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)
        (algebraMap K (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)))) n) :
    ∃ (i : MonomialCoefficientChartIndex300 3 n)
      (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K),
      originalCoefficientTestPhysicalFamily317 R n r hr j hn i q = Q := by
  obtain ⟨i, q, hq⟩ := originalFieldClassifier_coefficientChart_exists317 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) K
    (originalNormalizedAffineClassifyingMap317 R r hr j K n hn Q)
  refine ⟨i, q, ?_⟩
  apply originalNormalizedAffineClassifier_injective317 R r hr j K n hn
  exact (originalNormalizedAffinePointOfClassifier_classifies317 R r hr j K n hn
    (originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i q)).trans hq

end PfaffianDescent
end
