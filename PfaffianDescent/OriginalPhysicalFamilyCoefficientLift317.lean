import PfaffianDescent.OriginalCoefficientChartTestFamily317
import PfaffianDescent.NativeNilpotentCoefficientChartLift317

/-! SOURCE ONLY317. A PHYSICAL normalized family lift constructs the original
classifying diagram internally and therefore an AlgHom lift in the SAME
original-ground coefficient chart. This is an internal adapter, not a proof
that the required physical family lift exists in every original test. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Project a genuine Over diagram to native Scheme arrows before any
original normalized family/classifier/coefficient algebra is substituted. -/
private theorem physicalFamilyClassifierOver_left317
    {T : Scheme.{u}} {U V L : Over T}
    (a : U ⟶ V) (b : V ⟶ L) (c : U ⟶ L) (h : a ≫ b = c) :
    a.left ≫ b.left = c.left :=
  congrArg (fun f : U ⟶ L => f.left) h

variable (R : Type u) [CommRing R] (n : ℕ)
variable (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
variable (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
variable {B S : Type u} [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]

/-- The canonical physical coefficient test family has the ORIGINAL given
classifier, derived from the accepted inverse classification. This is a
proof cut, not an additional comparison premise for the final lift. -/
private theorem originalCoefficientPhysicalFamily_classifiesCut317
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] S) :
    originalNormalizedAffineClassifyingMap317 R r hr j S n hn
        (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q) =
      originalCoefficientTestClassifyingMap317 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i q :=
  originalNormalizedAffinePointOfClassifier_classifies317 R r hr j S n hn
    (originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i q)

variable (pi : B →ₐ[R] S)
variable (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
  (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] S)
variable (Q : FiniteFlatHilbertPoint195
  (Spec.map (CommRingCat.ofHom (R := B)
    (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R B)) j)
    (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R B)) j)))) n)
variable (hphysical : originalNormalizedAffinePointReduction317 R pi r hr j n Q =
  originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)

include hphysical

/-- Physical normalized reduction and accepted original-ground classifier
naturality DERIVE the reduction diagram as an Over equality. No diagram or
classifying-map lift is supplied separately from the physical family data. -/
lemma originalPhysicalFamilyClassifier_reductionOver317 :
    originalNormalizedAffineTestMap317 R pi ≫
        originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q =
      originalCoefficientTestClassifyingMap317 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i q :=
  (originalNormalizedAffineClassifyingMap_natural317 R pi r hr j n hn Q).symm.trans
    ((congrArg (originalNormalizedAffineClassifyingMap317 R r hr j S n hn) hphysical).trans
      (originalCoefficientPhysicalFamily_classifiesCut317 R n r hr j hn i q))

/-- The native original Spec pi/classifier/Spec q/chart diagram required by
nilpotent open-chart lifting. It is the left projection of the derived Over
diagram, with the SAME original quotient coefficient algebra and base R. -/
lemma originalPhysicalFamilyClassifier_reduction317 :
    Spec.map (CommRingCat.ofHom pi.toRingHom) ≫
        (originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q).left =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫
        monomialClosedCoefficientChartToLocus312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) i :=
  physicalFamilyClassifierOver_left317
    (originalNormalizedAffineTestMap317 R pi)
    (originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q)
    (originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i q)
    (originalPhysicalFamilyClassifier_reductionOver317 R n r hr j hn i pi q Q hphysical)

/-- The PHYSICAL normalized lift derives an exact AlgHom lift in the SAME
original coefficient chart. Surjective nilpotent reduction forces the whole
lifted classifier into that chart; accepted317 full faithfulness constructs l.
No desired algebra lift, classifier diagram or chart-factor premise is added. -/
lemma originalCoefficientChart_lift_of_physicalNormalizedFamily317
    (hpi : Function.Surjective pi)
    (hnil : IsNilpotent (RingHom.ker pi.toRingHom)) :
    ∃ l : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] B,
      pi.comp l = q ∧
      Spec.map (CommRingCat.ofHom l.toRingHom) ≫
        monomialClosedCoefficientChartToLocus312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) i =
        (originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q).left :=
  @monomialClosedCoefficientChart_lift_of_nilpotentClassifyingMap317
    R _ 3 n (originalNormalizedHypersurfacePolynomial312 r j) i B S _ _ _ _
    pi hpi hnil q
    (originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q).left
    (originalNormalizedAffineClassifyingMap317 R r hr j B n hn Q).w
    (originalPhysicalFamilyClassifier_reduction317 R n r hr j hn i pi q Q hphysical)

end PfaffianDescent
end
