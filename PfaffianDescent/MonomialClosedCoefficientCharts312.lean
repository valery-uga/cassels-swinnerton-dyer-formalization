import PfaffianDescent.MonomialPolynomialContainmentLocus310
import PfaffianDescent.NativeClosedChartBaseChange312
import PfaffianDescent.NativeSchemeCoverIsoCharts300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Literal quotient map by the original finite coefficient equations. -/
def monomialClosedCoefficientQuotientMap312 (i : MonomialCoefficientChartIndex300 m n) :
    UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R]
      MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i :=
  Ideal.Quotient.mkₐ R (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)

/-- Its native Spec map retains the original quotient ring and dictionaries. -/
def monomialClosedCoefficientQuotientSpec312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
      Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) :=
  Spec.map (CommRingCat.ofHom
    (R := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (S := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
    (monomialClosedCoefficientQuotientMap312 R m n p i).toRingHom)

private instance monomialClosedCoefficientQuotient_closed312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsClosedImmersion (monomialClosedCoefficientQuotientSpec312 R m n p i) :=
  monomialPolynomialContainmentCoefficient_isClosedImmersion310 R m n p i

/-- The constructed coefficient quotient maps to SAME original H. -/
def monomialClosedCoefficientToH312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
      monomialCoefficientGluedScheme300 R m n :=
  monomialClosedCoefficientQuotientSpec312 R m n p i ≫
    monomialCoefficientGluedChartMap300 R m n i

lemma monomialClosedCoefficientToH_overBase312 (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedCoefficientToH312 R m n p i ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) := by
  rw [monomialClosedCoefficientToH312, Category.assoc,
    monomialCoefficientGluedChartMap_toBase300]
  exact algebraHomSpecMap_overBase298 (monomialClosedCoefficientQuotientMap312 R m n p i)

/-- Constructed chart of the closed global locus, using its whole kernel equality. -/
def monomialClosedCoefficientChartToLocus312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ⟶
      monomialPolynomialContainmentLocus310 R m n p :=
  nativeClosedChartToGlobal312 (monomialPolynomialContainmentIdeal310 R m n p)
    (monomialCoefficientGluedChartMap300 R m n i)
    (monomialClosedCoefficientQuotientSpec312 R m n p i)
    (monomialPolynomialContainmentIdeal_chart310 R m n p i)

lemma monomialClosedCoefficientChartToLocus_comp312 (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedCoefficientChartToLocus312 R m n p i ≫
        monomialPolynomialContainmentLocusInclusion310 R m n p =
      monomialClosedCoefficientToH312 R m n p i :=
  nativeClosedChartToGlobal_comp312 _ _ _ _

lemma monomialClosedCoefficientChartToLocus_isPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialClosedCoefficientQuotientSpec312 R m n p i)
      (monomialClosedCoefficientChartToLocus312 R m n p i)
      (monomialCoefficientGluedChartMap300 R m n i)
      (monomialPolynomialContainmentLocusInclusion310 R m n p) :=
  nativeClosedChartToGlobal_isPullback312 _ _ _ _

/-- Presentation of the actual pulled-back H chart by the original equation quotient. -/
def monomialClosedCoefficientChartPullbackIso312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) ≅
      pullback (monomialPolynomialContainmentLocusInclusion310 R m n p)
        (monomialCoefficientGluedChartMap300 R m n i) :=
  (monomialClosedCoefficientChartToLocus_isPullback312 R m n p i).flip.isoPullback

lemma monomialClosedCoefficientChartPullbackIso_hom_fst312
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialClosedCoefficientChartPullbackIso312 R m n p i).hom ≫
        pullback.fst (monomialPolynomialContainmentLocusInclusion310 R m n p)
          (monomialCoefficientGluedChartMap300 R m n i) =
      monomialClosedCoefficientChartToLocus312 R m n p i :=
  (monomialClosedCoefficientChartToLocus_isPullback312 R m n p i).flip.isoPullback_hom_fst

/-- Actual open cover of the constructed locus by the original finite equation spectra. -/
def monomialClosedCoefficientLocusOpenCover312 :
    (monomialPolynomialContainmentLocus310 R m n p).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300
    ((monomialCoefficientGluedOpenCover300 R m n).pullback₁
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (fun i => Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i.down)))
    (fun i => monomialClosedCoefficientChartPullbackIso312 R m n p i.down)

lemma monomialClosedCoefficientLocusOpenCover_map312 (i : MonomialCoefficientChartIndex300 m n) :
    (monomialClosedCoefficientLocusOpenCover312 R m n p).f (ULift.up i) =
      monomialClosedCoefficientChartToLocus312 R m n p i :=
  monomialClosedCoefficientChartPullbackIso_hom_fst312 R m n p i

end PfaffianDescent
end
