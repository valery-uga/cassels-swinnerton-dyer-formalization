import PfaffianDescent.MonomialClosedCoefficientCharts312
import PfaffianDescent.MonomialPolynomialContainmentFamily310
import PfaffianDescent.FixedBaseTestAmbientMap305

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Original polynomial chart is Cartesian over the constructed locus chart. -/
lemma monomialClosedPolynomialChart_outerIsPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback
      (fixedBaseTestAmbientMap305 R m n (monomialClosedCoefficientToH312 R m n p i)
        (monomialClosedCoefficientToH_overBase312 R m n p i))
      (nativePolynomialProjection300 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m)
      (monomialCoefficientAmbientToH300 R m n)
      (monomialClosedCoefficientChartToLocus312 R m n p i ≫
        monomialPolynomialContainmentLocusInclusion310 R m n p) := by
  rw [monomialClosedCoefficientChartToLocus_comp312]
  exact fixedBaseTestAmbientMap_isPullback305 R m n _ _

/-- Literal polynomial spectrum maps to the global ambient after restriction to the locus. -/
def monomialClosedPolynomialChartToAmbient312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) ⟶
      monomialPolynomialContainmentAmbient310 R m n p :=
  nativeCartesianBaseChangeChartMap312
    (fixedBaseTestAmbientMap305 R m n (monomialClosedCoefficientToH312 R m n p i)
      (monomialClosedCoefficientToH_overBase312 R m n p i))
    (nativePolynomialProjection300 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m)
    (monomialClosedCoefficientChartToLocus312 R m n p i)
    (monomialCoefficientAmbientToH300 R m n)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)
    (monomialClosedPolynomialChart_outerIsPullback312 R m n p i)

lemma monomialClosedPolynomialChartToAmbient_fst312 (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedPolynomialChartToAmbient312 R m n p i ≫
        pullback.fst (monomialCoefficientAmbientToH300 R m n)
          (monomialPolynomialContainmentLocusInclusion310 R m n p) =
      fixedBaseTestAmbientMap305 R m n (monomialClosedCoefficientToH312 R m n p i)
        (monomialClosedCoefficientToH_overBase312 R m n p i) :=
  nativeCartesianBaseChangeChartMap_fst312 _ _ _ _ _ _

lemma monomialClosedPolynomialChartToAmbient_isPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialClosedPolynomialChartToAmbient312 R m n p i)
      (nativePolynomialProjection300 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m)
      (monomialPolynomialContainmentAmbientToLocus310 R m n p)
      (monomialClosedCoefficientChartToLocus312 R m n p i) :=
  nativeCartesianBaseChangeChartMap_isPullback312 _ _ _ _ _ _

private lemma monomialClosedPolynomialCoverChart_isPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialClosedPolynomialChartToAmbient312 R m n p i)
      (nativePolynomialProjection300 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m)
      (monomialPolynomialContainmentAmbientToLocus310 R m n p)
      ((monomialClosedCoefficientLocusOpenCover312 R m n p).f (ULift.up i)) := by
  rw [monomialClosedCoefficientLocusOpenCover_map312]
  exact monomialClosedPolynomialChartToAmbient_isPullback312 R m n p i

/-- Cover of the actual restricted ambient by actual polynomial spectra. -/
def monomialClosedPolynomialAmbientOpenCover312 :
    (monomialPolynomialContainmentAmbient310 R m n p).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300
    ((monomialClosedCoefficientLocusOpenCover312 R m n p).pullback₁
      (monomialPolynomialContainmentAmbientToLocus310 R m n p))
    (fun i => Spec (.of (MvPolynomial (Fin m)
      (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i.down))))
    (fun i => (monomialClosedPolynomialCoverChart_isPullback312 R m n p i.down).isoPullback)

lemma monomialClosedPolynomialAmbientOpenCover_map312 (i : MonomialCoefficientChartIndex300 m n) :
    (monomialClosedPolynomialAmbientOpenCover312 R m n p).f (ULift.up i) =
      monomialClosedPolynomialChartToAmbient312 R m n p i :=
  (monomialClosedPolynomialCoverChart_isPullback312 R m n p i).isoPullback_hom_fst

end PfaffianDescent
end
