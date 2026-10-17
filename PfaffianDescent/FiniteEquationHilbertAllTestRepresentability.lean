import PfaffianDescent.FiniteEquationHilbertWholeContainmentCriterion
import PfaffianDescent.RelativeClosedAmbientFiniteFlatFunctor313
import Mathlib.CategoryTheory.Types.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n r : ℕ) (q : Fin r → MvPolynomial (Fin m) R)
set_option autoImplicit false

/-- The finite-equation coefficient parameter scheme is constructed as the
actual closed subscheme of the SAME existing H, with its original R map. -/
def finiteEquationHilbertRepresentingObject001 : Over (Spec (.of R)) :=
  Over.mk ((finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι ≫
    monomialCoefficientGluedToBase300 R m n)

/-- Its actual original-H inclusion, retaining the original base equality. -/
def finiteEquationHilbertRepresentingInclusion001 :
    finiteEquationHilbertRepresentingObject001 R m n r q ⟶
      monomialCoefficientRepresentingObject309 R m n :=
  Over.homMk (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι rfl

/-- Canonical whole-ideal factor in the original slice, used with a condition
derived internally from each actual family's physical defining equations. -/
def finiteEquationRelativeLocusFactor001
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (h : finiteEquationHilbertCoefficientIdeal001 R m n r q ≤ g.left.ker) :
    T ⟶ finiteEquationHilbertRepresentingObject001 R m n r q :=
  Over.homMk (nativeClosedSubschemeFactor312
    (finiteEquationHilbertCoefficientIdeal001 R m n r q) g.left h) (by
      change nativeClosedSubschemeFactor312 _ g.left h ≫
        ((finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι ≫
          monomialCoefficientGluedToBase300 R m n) = T.hom
      exact (Category.assoc
        (nativeClosedSubschemeFactor312 (finiteEquationHilbertCoefficientIdeal001 R m n r q) g.left h)
        (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι
        (monomialCoefficientGluedToBase300 R m n)).symm.trans
          ((congrArg (fun k : T.left ⟶ monomialCoefficientGluedScheme300 R m n =>
              k ≫ monomialCoefficientGluedToBase300 R m n)
            (nativeClosedSubschemeFactor_comp312
              (finiteEquationHilbertCoefficientIdeal001 R m n r q) g.left h)).trans (Over.w g)))

/-- The constructed slice factor preserves EXACTLY the original classifier map. -/
theorem finiteEquationRelativeLocusFactor_comp001
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (h : finiteEquationHilbertCoefficientIdeal001 R m n r q ≤ g.left.ker) :
    finiteEquationRelativeLocusFactor001 R m n r q T g h ≫
        finiteEquationHilbertRepresentingInclusion001 R m n r q = g := by
  apply Over.OverMorphism.ext
  exact nativeClosedSubschemeFactor_comp312 _ _ _

/-- A map to the constructed locus produces the SAME universal whole family,
with physical containment of the original ENTIRE finite-equation quotient derived. -/
def finiteEquationRelativeLocusUniversalContainedPoint001
    (T : Over (Spec (.of R))) (d : T ⟶ finiteEquationHilbertRepresentingObject001 R m n r q) :
    relativeClosedAmbientContainedPoint313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n T := by
  let g := d ≫ finiteEquationHilbertRepresentingInclusion001 R m n r q
  have h : finiteEquationHilbertCoefficientIdeal001 R m n r q ≤ g.left.ker := by
    change finiteEquationHilbertCoefficientIdeal001 R m n r q ≤
      (d.left ≫ (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι).ker
    exact (finiteEquationHilbertCoefficientIdeal001 R m n r q).ker_subschemeι.symm.le.trans
      (d.left.le_ker_comp (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι)
  refine ⟨monomialRelativeUniversalPullback309 R m n T g, ?_⟩
  change finiteEquationRelativeOriginalPolynomialIdeal001 R m r q T ≤
    (monomialRelativeUniversalPullback309 R m n T g).val
  exact (finiteEquationRelativeUniversalContainment_locusKernel_iff001 R m n r q T g).mp h

/-- The actual contained family's original classifier factors through the
constructed finite-equation locus. No classifier or coefficient outcome is supplied. -/
def finiteEquationRelativeContainedHilbertClassifyingMap001
    (hn : 0 < n) (T : Over (Spec (.of R)))
    (P : relativeClosedAmbientContainedPoint313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n T) :
    T ⟶ finiteEquationHilbertRepresentingObject001 R m n r q :=
  finiteEquationRelativeLocusFactor001 R m n r q T
    (relativeNativeGlobalClassifyingMap311 R m n T hn P.val)
    (finiteEquationOriginalContainedHilbertPoint_classifier_locusKernel001 R m n r q T hn
      P.val P.property)

/-- The classifier retains the exact original ambient classifier after inclusion. -/
theorem finiteEquationRelativeContainedHilbertClassifyingMap_comp001
    (hn : 0 < n) (T : Over (Spec (.of R)))
    (P : relativeClosedAmbientContainedPoint313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n T) :
    finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T P ≫
        finiteEquationHilbertRepresentingInclusion001 R m n r q =
      relativeNativeGlobalClassifyingMap311 R m n T hn P.val :=
  finiteEquationRelativeLocusFactor_comp001 R m n r q T
    (relativeNativeGlobalClassifyingMap311 R m n T hn P.val)
    (finiteEquationOriginalContainedHilbertPoint_classifier_locusKernel001 R m n r q T hn
      P.val P.property)

/-- Genuine ALL-test classification by the constructed finite-equation locus,
with inverse the original universal WHOLE-family pullback. -/
def finiteEquationRelativeContainedHilbertClassificationEquiv001
    (hn : 0 < n) (T : Over (Spec (.of R))) :
    relativeClosedAmbientContainedPoint313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n T ≃
        (T ⟶ finiteEquationHilbertRepresentingObject001 R m n r q) where
  toFun := finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T
  invFun := finiteEquationRelativeLocusUniversalContainedPoint001 R m n r q T
  left_inv P := by
    apply Subtype.ext
    change monomialRelativeUniversalPullback309 R m n T
      (finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T P ≫
        finiteEquationHilbertRepresentingInclusion001 R m n r q) = P.val
    rw [finiteEquationRelativeContainedHilbertClassifyingMap_comp001]
    exact (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P.val).symm
  right_inv d := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι).mp
    have he := finiteEquationRelativeContainedHilbertClassifyingMap_comp001 R m n r q hn T
      (finiteEquationRelativeLocusUniversalContainedPoint001 R m n r q T d)
    have hg := (relativeNativeHilbertClassificationEquiv311 R m n hn T).right_inv
      (d ≫ finiteEquationHilbertRepresentingInclusion001 R m n r q)
    exact congrArg (fun z : T ⟶ monomialCoefficientRepresentingObject309 R m n => z.left)
      (he.trans hg)

/-- EVERY original test map preserves the classifier, proved using its actual
whole-family naturality and the monomorphism of the constructed closed locus. -/
theorem finiteEquationRelativeContainedHilbertClassifyingMap_natural001
    (hn : 0 < n) {T0 T1 : Over (Spec (.of R))} (a : T0 ⟶ T1)
    (P : relativeClosedAmbientContainedPoint313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n T1) :
    finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T0
        (relativeClosedAmbientContainedPointMap313
          (finiteEquationOriginalPolynomialEmbedding001 R m r q)
          (nativePolynomialProjection300 R m) n a P) =
      a ≫ finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T1 P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (finiteEquationHilbertCoefficientIdeal001 R m n r q).subschemeι).mp
  have he : finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T0
      (relativeClosedAmbientContainedPointMap313
        (finiteEquationOriginalPolynomialEmbedding001 R m r q)
        (nativePolynomialProjection300 R m) n a P) ≫
      finiteEquationHilbertRepresentingInclusion001 R m n r q =
    (a ≫ finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T1 P) ≫
      finiteEquationHilbertRepresentingInclusion001 R m n r q := by
    rw [finiteEquationRelativeContainedHilbertClassifyingMap_comp001, Category.assoc,
      finiteEquationRelativeContainedHilbertClassifyingMap_comp001]
    exact relativeNativeGlobalClassifyingMap_natural311 R m n hn a P.val
  exact congrArg (fun z : T0 ⟶ monomialCoefficientRepresentingObject309 R m n => z.left) he

/-- Constructed ALL-native-test representing NatIso for finite-equation whole
containment; no representability or desired naturality is a premise. -/
def finiteEquationRelativeContainedHilbertRepresentingIso001 (hn : 0 < n) :
    relativeClosedAmbientContainedFunctor313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
      (nativePolynomialProjection300 R m) n ≅
        yoneda.obj (finiteEquationHilbertRepresentingObject001 R m n r q) :=
  NatIso.ofComponents
    (fun T => (finiteEquationRelativeContainedHilbertClassificationEquiv001 R m n r q hn T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro P
      change finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T1.unop
          (relativeClosedAmbientContainedPointMap313
            (finiteEquationOriginalPolynomialEmbedding001 R m r q)
            (nativePolynomialProjection300 R m) n a.unop P) =
        a.unop ≫ finiteEquationRelativeContainedHilbertClassifyingMap001 R m n r q hn T0.unop P
      exact finiteEquationRelativeContainedHilbertClassifyingMap_natural001 R m n r q hn a.unop P)

/-- The literal ORIGINAL quotient's finite-flat functor is represented by the
constructed SAME-H locus on all scheme tests, preserving original R and nilpotents. -/
def finiteEquationOriginalQuotientHilbertRepresentingIso001 (hn : 0 < n) :
    relativeFiniteFlatHilbertFunctor197
      (finiteEquationOriginalPolynomialEmbedding001 R m r q ≫ nativePolynomialProjection300 R m) n ≅
        yoneda.obj (finiteEquationHilbertRepresentingObject001 R m n r q) := by
  letI := finiteEquationOriginalPolynomialEmbedding_isClosedImmersion001 R m r q
  exact relativeClosedAmbientFiniteFlatFunctorIso313
      (finiteEquationOriginalPolynomialEmbedding001 R m r q) (nativePolynomialProjection300 R m) n ≪≫
    finiteEquationRelativeContainedHilbertRepresentingIso001 R m n r q hn

/-- The inverse classifier recovers the ENTIRE original universal ambient ideal.
This exact equality retains the original quotient/test/parameter maps and nilpotents. -/
theorem finiteEquationOriginalQuotientHilbertRepresentingIso_inv_ambientIdeal001
    (hn : 0 < n) (T : Over (Spec (.of R)))
    (d : T ⟶ finiteEquationHilbertRepresentingObject001 R m n r q) :
    ((finiteEquationOriginalQuotientHilbertRepresentingIso001 R m n r q hn).inv.app (.op T) d).val.map
        (relativeClosedAmbientTestMap313 (finiteEquationOriginalPolynomialEmbedding001 R m r q)
          (nativePolynomialProjection300 R m) T) =
      (monomialRelativeUniversalPullback309 R m n T
        (d ≫ finiteEquationHilbertRepresentingInclusion001 R m n r q)).val := by
  letI := finiteEquationOriginalPolynomialEmbedding_isClosedImmersion001 R m r q
  exact relativeClosedAmbientFiniteFlatFunctorIso_inv_ambientIdeal313
    (finiteEquationOriginalPolynomialEmbedding001 R m r q) (nativePolynomialProjection300 R m) n T
    (finiteEquationRelativeLocusUniversalContainedPoint001 R m n r q T d)

end PfaffianDescent
