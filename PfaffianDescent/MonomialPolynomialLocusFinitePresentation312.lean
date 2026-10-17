import PfaffianDescent.MonomialRelativeLocusContainedClassification312
import PfaffianDescent.NativeAlgebraSpecFinitePresentation307
import PfaffianDescent.UniversalCyclicMatrixQuotient282

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

private theorem nativeCoefficientQuotientFinitePresentation312
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] (I : Ideal C) (h : I.FG) :
    Algebra.FinitePresentation R (C ⧸ I) :=
  Algebra.FinitePresentation.quotient (R := R) h

private lemma nativePolynomialLocusLFPMapTransport312
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (hg : LocallyOfFinitePresentation g) : LocallyOfFinitePresentation f := by
  cases h
  exact hg

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Original closed coefficient quotient is finitely presented over original R;
finite equations310 and original coefficient presentation282 supply every intake. -/
theorem monomialPolynomialContainmentCoefficientAlgebra_finitePresentation312
    (i : MonomialCoefficientChartIndex300 m n) :
    Algebra.FinitePresentation R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) := by
  letI : Algebra.FinitePresentation R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) :=
    universalCyclicCoefficientAlgebra_finitePresentation282 R m n i.monomials i.zeroIndex
  exact nativeCoefficientQuotientFinitePresentation312 R
    (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)
    (monomialPolynomialContainmentCoefficientIdeal_fg310 R m n p i)

lemma monomialPolynomialContainmentCoefficientSpec_locallyOfFinitePresentation312
    (i : MonomialCoefficientChartIndex300 m n) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)))) := by
  letI := monomialPolynomialContainmentCoefficientAlgebra_finitePresentation312 R m n p i
  exact nativeAlgebraSpecProjection_locallyOfFinitePresentation307 R
    (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)

/-- The actual closed-locus coefficient chart retains its ORIGINAL scalar map. -/
lemma monomialPolynomialContainmentChart_toBase312 (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedCoefficientChartToLocus312 R m n p i ≫
        (monomialPolynomialContainmentRepresentingObject312 R m n p).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) :=
  (Category.assoc (monomialClosedCoefficientChartToLocus312 R m n p i)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)
    (monomialCoefficientGluedToBase300 R m n)).symm.trans
      ((congrArg
        (fun q : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
            monomialCoefficientGluedScheme300 R m n => q ≫ monomialCoefficientGluedToBase300 R m n)
        (monomialClosedCoefficientChartToLocus_comp312 R m n p i)).trans
          (monomialClosedCoefficientToH_overBase312 R m n p i))

/-- Constructed SAME-H closed polynomial coefficient locus is LFP over R,
proved on its ACTUAL internally constructed equation-quotient cover. -/
theorem monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 :
    LocallyOfFinitePresentation (monomialPolynomialContainmentRepresentingObject312 R m n p).hom := by
  apply nativeLocallyOfFinitePresentation_of_sourceOpenCover307
    (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
    (monomialClosedCoefficientLocusOpenCover312 R m n p)
  intro k
  change ULift (MonomialCoefficientChartIndex300 m n) at k
  let i := k.down
  have hlocal : LocallyOfFinitePresentation
      (monomialClosedCoefficientChartToLocus312 R m n p i ≫
        (monomialPolynomialContainmentRepresentingObject312 R m n p).hom) :=
    nativePolynomialLocusLFPMapTransport312 (monomialPolynomialContainmentChart_toBase312 R m n p i)
      (monomialPolynomialContainmentCoefficientSpec_locallyOfFinitePresentation312 R m n p i)
  exact Eq.mpr
    (congrArg
      (fun f : Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
          monomialPolynomialContainmentLocus310 R m n p =>
        LocallyOfFinitePresentation (f ≫ (monomialPolynomialContainmentRepresentingObject312 R m n p).hom))
      (monomialClosedCoefficientLocusOpenCover_map312 R m n p i)) hlocal

end PfaffianDescent
end
