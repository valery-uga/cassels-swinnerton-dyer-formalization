import PfaffianDescent.MonomialClosedPolynomialAmbientCharts312
import PfaffianDescent.NativeHypersurfaceAmbientIdeal312
import PfaffianDescent.NativeFixedBaseUniversalFamilyPullback305

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- The actual287 quotient coefficient point is the same entire297 specialized ideal. -/
lemma monomialClosedCoefficientWholeChart_eq312 (i : MonomialCoefficientChartIndex300 m n) :
    cyclicCoefficientWholeIdealChartEquiv287
        (A := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
        i.monomials i.zeroIndex R i.zero_eq (monomialClosedCoefficientQuotientMap312 R m n p i) =
      monomialPolynomialContainmentChartWholeIdeal310 R m n p i := by
  change cyclicMatrixWholeIdealChart287 i.monomials i.zeroIndex
      (cyclicCoefficientPoint283 R m n i.monomials i.zeroIndex
        (monomialClosedCoefficientQuotientMap312 R m n p i)) =
    cyclicMatrixWholeIdealChart287 i.monomials i.zeroIndex
      (cyclicMatrixPointMap287 i.monomials i.zeroIndex
        (monomialClosedCoefficientQuotientMap312 R m n p i).toRingHom
        (monomialUniversalCoefficientPoint310 R m n i))
  rw [monomialUniversalCoefficientPoint_specialize310]

/-- Reverse305 agrees with the exact genuine quotient family on the closed coefficient chart. -/
lemma monomialClosedCoefficientUniversalPullback_wholeIdeal312
    (i : MonomialCoefficientChartIndex300 m n) :
    (fixedBaseUniversalFamilyPullback305 R m n (monomialClosedCoefficientToH312 R m n p i)
        (monomialClosedCoefficientToH_overBase312 R m n p i)).val =
      (monomialWholeIdealNativeFamily302 i.monomials
        (monomialPolynomialContainmentChartWholeIdeal310 R m n p i)).val := by
  have hf : Spec.map (CommRingCat.ofHom
      (AlgHom.id R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)).toRingHom) ≫
        monomialClosedCoefficientToH312 R m n p i =
      Spec.map (CommRingCat.ofHom (monomialClosedCoefficientQuotientMap312 R m n p i).toRingHom) ≫
        monomialCoefficientGluedChartMap300 R m n i := by
    change Spec.map (CommRingCat.ofHom (RingHom.id
        (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) ≫
        monomialClosedCoefficientToH312 R m n p i = _
    rw [nativeSpecRingId312 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i),
      Category.id_comp]
    rfl
  have h := fixedBaseUniversalFamilyPullback_chartIdeal305 R m n
    (monomialClosedCoefficientToH312 R m n p i)
    (monomialClosedCoefficientToH_overBase312 R m n p i) i
    (AlgHom.id R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
    (monomialClosedCoefficientQuotientMap312 R m n p i) hf
  rw [nativePolynomialSpecId312, Scheme.IdealSheafData.comap_id] at h
  rw [cyclicCoefficientUniversalFamily_classifies302 R
    (A := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
    i.monomials i.zeroIndex i.zero_eq (monomialClosedCoefficientQuotientMap312 R m n p i),
    monomialClosedCoefficientWholeChart_eq312 R m n p i] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricted global universal whole ideal agrees with the same original297 quotient chart. -/
lemma monomialRestrictedUniversalFamily_chartWholeIdeal312
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val.comap
        (monomialClosedPolynomialChartToAmbient312 R m n p i) =
      (monomialWholeIdealNativeFamily302 i.monomials
        (monomialPolynomialContainmentChartWholeIdeal310 R m n p i)).val := by
  have hr := congrArg
    (fun I : (monomialPolynomialContainmentAmbient310 R m n p).IdealSheafData =>
      I.comap (monomialClosedPolynomialChartToAmbient312 R m n p i))
    (monomialPolynomialContainmentRestrictedUniversalFamily_wholeIdeal310 R m n p)
  have hc := (monomialCoefficientUniversalWholeIdeal300 R m n).comap_comp
    (monomialClosedPolynomialChartToAmbient312 R m n p i)
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
  have hf := congrArg (monomialCoefficientUniversalWholeIdeal300 R m n).comap
    (monomialClosedPolynomialChartToAmbient_fst312 R m n p i)
  exact hr.trans (hc.symm.trans (hf.trans
    (monomialClosedCoefficientUniversalPullback_wholeIdeal312 R m n p i)))

/-- The genuine297 hypersurface family and the restricted global universal family
retain equal entire ideals in the original polynomial ambient on each actual chart. -/
lemma monomialRestrictedUniversalFamily_chartHypersurfaceAmbientIdeal312
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialContainmentChartHypersurfaceFamily310 R m n p i).val.map
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span
          {MvPolynomial.map
            (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))) =
      (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val.comap
        (monomialClosedPolynomialChartToAmbient312 R m n p i) :=
  (affineHypersurfaceWholeQuotientHilbertPoint_ambientIdeal312 _ _ _ _).trans
    (monomialRestrictedUniversalFamily_chartWholeIdeal312 R m n p i).symm

end PfaffianDescent
end
