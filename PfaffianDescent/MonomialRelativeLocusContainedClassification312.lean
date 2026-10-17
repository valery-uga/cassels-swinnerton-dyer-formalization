import PfaffianDescent.MonomialAllTestPolynomialLocusCriterion312
import PfaffianDescent.RelativeClosedAmbientFiniteFlatFunctor313

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Literal original polynomial hypersurface embedding, with the original quotient. -/
def monomialOriginalPolynomialHypersurfaceEmbedding312 :
    Spec (.of (MvPolynomial (Fin m) R ⧸ Ideal.span {p})) ⟶ Spec (.of (MvPolynomial (Fin m) R)) :=
  Spec.map (CommRingCat.ofHom (R := MvPolynomial (Fin m) R)
    (S := MvPolynomial (Fin m) R ⧸ Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p})))

private instance monomialOriginalPolynomialHypersurfaceEmbedding_closed312 :
    IsClosedImmersion (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Actual constructed coefficient locus, as an object over original Spec R. -/
def monomialPolynomialContainmentRepresentingObject312 : Over (Spec (.of R)) :=
  Over.mk (monomialPolynomialContainmentLocusInclusion310 R m n p ≫
    monomialCoefficientGluedToBase300 R m n)

def monomialPolynomialContainmentRepresentingInclusion312 :
    monomialPolynomialContainmentRepresentingObject312 R m n p ⟶
      monomialCoefficientRepresentingObject309 R m n :=
  Over.homMk (monomialPolynomialContainmentLocusInclusion310 R m n p) rfl

private instance monomialPolynomialContainmentLocusEmbedding_closed312 :
    IsClosedImmersion (monomialPolynomialContainmentLocusInclusion310 R m n p) :=
  monomialPolynomialContainmentLocusInclusion_isClosedImmersion310 R m n p

/-- Native slice factor uses the proved actual whole-locus kernel condition. -/
def monomialRelativeLocusFactor312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (h : monomialPolynomialContainmentIdeal310 R m n p ≤ g.left.ker) :
    T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p :=
  Over.homMk (nativeClosedSubschemeFactor312 (monomialPolynomialContainmentIdeal310 R m n p)
    g.left h) (by
      change nativeClosedSubschemeFactor312 _ g.left h ≫
        (monomialPolynomialContainmentLocusInclusion310 R m n p ≫
          monomialCoefficientGluedToBase300 R m n) = T.hom
      exact (Category.assoc
        (nativeClosedSubschemeFactor312 (monomialPolynomialContainmentIdeal310 R m n p) g.left h)
        (monomialPolynomialContainmentLocusInclusion310 R m n p)
        (monomialCoefficientGluedToBase300 R m n)).symm.trans
          ((congrArg (fun f : T.left ⟶ monomialCoefficientGluedScheme300 R m n =>
              f ≫ monomialCoefficientGluedToBase300 R m n)
            (nativeClosedSubschemeFactor_comp312 (monomialPolynomialContainmentIdeal310 R m n p)
              g.left h)).trans (Over.w g)))

lemma monomialRelativeLocusFactor_comp312
    (T : Over (Spec (.of R))) (g : T ⟶ monomialCoefficientRepresentingObject309 R m n)
    (h : monomialPolynomialContainmentIdeal310 R m n p ≤ g.left.ker) :
    monomialRelativeLocusFactor312 R m n p T g h ≫
        monomialPolynomialContainmentRepresentingInclusion312 R m n p = g := by
  apply Over.OverMorphism.ext
  exact nativeClosedSubschemeFactor_comp312 _ _ _

/-- A locus morphism produces the literal whole universal ambient pullback,
with physical polynomial containment proved by the actual all-test criterion. -/
def monomialRelativeLocusUniversalContainedPoint312 (T : Over (Spec (.of R)))
    (d : T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p) :
    relativeClosedAmbientContainedPoint313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n T :=
  ⟨monomialRelativeUniversalPullback309 R m n T
      (d ≫ monomialPolynomialContainmentRepresentingInclusion312 R m n p),
    monomialRelativeUniversalContainment_of_locusFactor312 R m n p T
      (d ≫ monomialPolynomialContainmentRepresentingInclusion312 R m n p) d.left rfl⟩

/-- Original ambient classifier factors through the constructed closed locus;
its coefficient containment is derived from the ORIGINAL whole polynomial ideal. -/
def monomialRelativeContainedHilbertClassifyingMap312 (hn : 0 < n)
    (T : Over (Spec (.of R)))
    (P : relativeClosedAmbientContainedPoint313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n T) :
    T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p :=
  monomialRelativeLocusFactor312 R m n p T
    (relativeNativeGlobalClassifyingMap311 R m n T hn P.val)
    (originalRelativeContainedHilbertPoint_classifier_locusKernel312 R m n p T hn P.val P.property)

lemma monomialRelativeContainedHilbertClassifyingMap_comp312 (hn : 0 < n)
    (T : Over (Spec (.of R)))
    (P : relativeClosedAmbientContainedPoint313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n T) :
    monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T P ≫
        monomialPolynomialContainmentRepresentingInclusion312 R m n p =
      relativeNativeGlobalClassifyingMap311 R m n T hn P.val :=
  monomialRelativeLocusFactor_comp312 R m n p T
    (relativeNativeGlobalClassifyingMap311 R m n T hn P.val)
    (originalRelativeContainedHilbertPoint_classifier_locusKernel312 R m n p T hn P.val P.property)

/-- Genuine classification of the whole polynomial-contained ambient subfunctor,
on ALL original-base test schemes, by the actual closed coefficient locus. -/
def monomialRelativeContainedHilbertClassificationEquiv312 (hn : 0 < n)
    (T : Over (Spec (.of R))) :
    relativeClosedAmbientContainedPoint313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n T ≃
      (T ⟶ monomialPolynomialContainmentRepresentingObject312 R m n p) where
  toFun := monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T
  invFun := monomialRelativeLocusUniversalContainedPoint312 R m n p T
  left_inv P := by
    apply Subtype.ext
    change monomialRelativeUniversalPullback309 R m n T
      (monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T P ≫
        monomialPolynomialContainmentRepresentingInclusion312 R m n p) = P.val
    rw [monomialRelativeContainedHilbertClassifyingMap_comp312]
    exact (relativeNativeGlobalClassifyingMap_pullback311 R m n T hn P.val).symm
  right_inv d := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (monomialPolynomialContainmentLocusInclusion310 R m n p)).mp
    have he := monomialRelativeContainedHilbertClassifyingMap_comp312 R m n p hn T
      (monomialRelativeLocusUniversalContainedPoint312 R m n p T d)
    have hg := (relativeNativeHilbertClassificationEquiv311 R m n hn T).right_inv
      (d ≫ monomialPolynomialContainmentRepresentingInclusion312 R m n p)
    exact congrArg (fun q : T ⟶ monomialCoefficientRepresentingObject309 R m n => q.left)
      (he.trans hg)

/-- Arbitrary test maps preserve the actual locus classifier. -/
lemma monomialRelativeContainedHilbertClassifyingMap_natural312 (hn : 0 < n)
    {T0 T1 : Over (Spec (.of R))} (a : T0 ⟶ T1)
    (P : relativeClosedAmbientContainedPoint313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n T1) :
    monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T0
        (relativeClosedAmbientContainedPointMap313
          (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
          (nativePolynomialProjection300 R m) n a P) =
      a ≫ monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T1 P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (monomialPolynomialContainmentLocusInclusion310 R m n p)).mp
  have he : monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T0
      (relativeClosedAmbientContainedPointMap313
        (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
        (nativePolynomialProjection300 R m) n a P) ≫
        monomialPolynomialContainmentRepresentingInclusion312 R m n p =
      (a ≫ monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T1 P) ≫
        monomialPolynomialContainmentRepresentingInclusion312 R m n p := by
    rw [monomialRelativeContainedHilbertClassifyingMap_comp312, Category.assoc,
      monomialRelativeContainedHilbertClassifyingMap_comp312]
    exact relativeNativeGlobalClassifyingMap_natural311 R m n hn a P.val
  exact congrArg (fun q : T0 ⟶ monomialCoefficientRepresentingObject309 R m n => q.left) he

/-- Genuine all-test representing NatIso for the whole polynomial-contained
ambient subfunctor; maps and inverses retain the original universal whole family. -/
def monomialRelativeContainedHilbertRepresentingIso312 (hn : 0 < n) :
    relativeClosedAmbientContainedFunctor313 (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
      (nativePolynomialProjection300 R m) n ≅
        yoneda.obj (monomialPolynomialContainmentRepresentingObject312 R m n p) :=
  NatIso.ofComponents
    (fun T => (monomialRelativeContainedHilbertClassificationEquiv312 R m n p hn T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro P
      change monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T1.unop
          (relativeClosedAmbientContainedPointMap313
            (monomialOriginalPolynomialHypersurfaceEmbedding312 R m p)
            (nativePolynomialProjection300 R m) n a.unop P) =
        a.unop ≫ monomialRelativeContainedHilbertClassifyingMap312 R m n p hn T0.unop P
      exact monomialRelativeContainedHilbertClassifyingMap_natural312 R m n p hn a.unop P)

end PfaffianDescent
end
