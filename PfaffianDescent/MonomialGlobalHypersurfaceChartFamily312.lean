import PfaffianDescent.MonomialGlobalHypersurfaceFamily312
import PfaffianDescent.NativeClosedChartBaseChange312
import PfaffianDescent.NativeClosedWholeIdealBaseChange313
import PfaffianDescent.NativeClosedFiniteFlatPointEquiv313

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeHypersurfaceQuotientProjection312
    (A : Type u) [CommRing A] (m : ℕ) (p : MvPolynomial (Fin m) A) :
    Spec.map (CommRingCat.ofHom (R := MvPolynomial (Fin m) A)
        (S := MvPolynomial (Fin m) A ⧸ Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}))) ≫
      nativePolynomialProjection300 A m =
    Spec.map (CommRingCat.ofHom (R := A)
      (S := MvPolynomial (Fin m) A ⧸ Ideal.span {p})
      (algebraMap A (MvPolynomial (Fin m) A ⧸ Ideal.span {p}))) := by
  rw [nativePolynomialProjection300, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Original-p=0 native quotient embedding on the actual closed coefficient chart. -/
def monomialClosedHypersurfaceChartEmbedding312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
      Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})) ⟶
      Spec (.of (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))) :=
  Spec.map (CommRingCat.ofHom
    (R := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
    (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
      Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
    (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map
      (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))

private instance monomialClosedHypersurfaceChartEmbedding_closed312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsClosedImmersion (monomialClosedHypersurfaceChartEmbedding312 R m n p i) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom
      (R := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
      (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
        Ideal.span {MvPolynomial.map
          (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
      (Ideal.Quotient.mk (Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))
    Ideal.Quotient.mk_surjective

/-- Exact original297 structural map of the actual local hypersurface. -/
def monomialClosedHypersurfaceChartProjection312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
      Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})) ⟶
      Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) :=
  Spec.map (CommRingCat.ofHom (R := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
    (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
      Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
    (algebraMap (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
      (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
        Ideal.span {MvPolynomial.map
          (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))

lemma monomialClosedHypersurfaceChartEmbedding_toCoefficient312
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedHypersurfaceChartEmbedding312 R m n p i ≫
        nativePolynomialProjection300 (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) m =
      monomialClosedHypersurfaceChartProjection312 R m n p i :=
  nativeHypersurfaceQuotientProjection312 _ m _

/-- Actual original quotient chart of the global native original-p=0 ambient. -/
def monomialClosedHypersurfaceChartToGlobal312 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
      Ideal.span {MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})) ⟶
      (monomialPolynomialHypersurfaceIdeal312 R m n p).subscheme :=
  nativeClosedChartToGlobal312 (monomialPolynomialHypersurfaceIdeal312 R m n p)
    (monomialClosedPolynomialChartToAmbient312 R m n p i)
    (monomialClosedHypersurfaceChartEmbedding312 R m n p i)
    (monomialPolynomialHypersurfaceIdeal_chart312 R m n p i)

lemma monomialClosedHypersurfaceChartToGlobal_comp312
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialClosedHypersurfaceChartToGlobal312 R m n p i ≫
        (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι =
      monomialClosedHypersurfaceChartEmbedding312 R m n p i ≫
        monomialClosedPolynomialChartToAmbient312 R m n p i :=
  nativeClosedChartToGlobal_comp312 _ _ _ _

lemma monomialClosedHypersurfaceChartToGlobal_isPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialClosedHypersurfaceChartEmbedding312 R m n p i)
      (monomialClosedHypersurfaceChartToGlobal312 R m n p i)
      (monomialClosedPolynomialChartToAmbient312 R m n p i)
      (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι :=
  nativeClosedChartToGlobal_isPullback312 _ _ _ _

/-- Genuine local hypersurface family square over the actual closed coefficient locus. -/
lemma monomialClosedHypersurfaceChartToGlobal_familyIsPullback312
    (i : MonomialCoefficientChartIndex300 m n) :
    IsPullback (monomialClosedHypersurfaceChartToGlobal312 R m n p i)
      (monomialClosedHypersurfaceChartProjection312 R m n p i)
      ((monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
        monomialPolynomialContainmentAmbientToLocus310 R m n p)
      (monomialClosedCoefficientChartToLocus312 R m n p i) := by
  have h := (monomialClosedHypersurfaceChartToGlobal_isPullback312 R m n p i).flip.paste_vert
    (monomialClosedPolynomialChartToAmbient_isPullback312 R m n p i)
  exact Eq.mp
    (congrArg
      (fun f : Spec (.of (MvPolynomial (Fin m)
          (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
            Ideal.span {MvPolynomial.map
              (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})) ⟶
          Spec (.of (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) =>
        IsPullback (monomialClosedHypersurfaceChartToGlobal312 R m n p i) f
          ((monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
            monomialPolynomialContainmentAmbientToLocus310 R m n p)
          (monomialClosedCoefficientChartToLocus312 R m n p i))
      (monomialClosedHypersurfaceChartEmbedding_toCoefficient312 R m n p i)) h

/-- Whole ideals INSIDE the original hypersurface agree with the genuine297 family;
closed pushforward reflects equality, so nilpotents are retained. -/
lemma monomialPolynomialHypersurfaceGlobalFamily_chartWholeIdeal312
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val.comap
        (monomialClosedHypersurfaceChartToGlobal312 R m n p i) =
      (monomialPolynomialContainmentChartHypersurfaceFamily310 R m n p i).val := by
  apply nativeWholeIdeal_map_closed_injective313
    (monomialClosedHypersurfaceChartEmbedding312 R m n p i)
  have hb := nativeClosedWholeIdeal_map_comap313
    (monomialClosedHypersurfaceChartToGlobal312 R m n p i)
    (monomialClosedHypersurfaceChartEmbedding312 R m n p i)
    (monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι
    (monomialClosedPolynomialChartToAmbient312 R m n p i)
    (monomialClosedHypersurfaceChartToGlobal_isPullback312 R m n p i).flip
    (monomialPolynomialHypersurfaceGlobalFamily312 R m n p).val
  have hg := congrArg
    (fun J : (monomialPolynomialContainmentAmbient310 R m n p).IdealSheafData =>
      J.comap (monomialClosedPolynomialChartToAmbient312 R m n p i))
    (monomialPolynomialHypersurfaceGlobalFamily_ambientIdeal312 R m n p)
  exact hb.trans (hg.trans
    (monomialRestrictedUniversalFamily_chartHypersurfaceAmbientIdeal312 R m n p i).symm)

/-- Actual native finite-flat restriction to the original local hypersurface chart. -/
def monomialPolynomialHypersurfaceGlobalFamily_chart312
    (i : MonomialCoefficientChartIndex300 m n) :
    FiniteFlatHilbertPoint195 (monomialClosedHypersurfaceChartProjection312 R m n p i) n :=
  finiteFlatHilbertBaseChange195 (monomialClosedHypersurfaceChartToGlobal312 R m n p i)
    (monomialClosedHypersurfaceChartProjection312 R m n p i)
    ((monomialPolynomialHypersurfaceIdeal312 R m n p).subschemeι ≫
      monomialPolynomialContainmentAmbientToLocus310 R m n p)
    (monomialClosedCoefficientChartToLocus312 R m n p i)
    (monomialClosedHypersurfaceChartToGlobal_familyIsPullback312 R m n p i) n
    (monomialPolynomialHypersurfaceGlobalFamily312 R m n p)

/-- Genuine family equality INSIDE the original hypersurface, not only after ambient image. -/
lemma monomialPolynomialHypersurfaceGlobalFamily_chart_eq297312
    (i : MonomialCoefficientChartIndex300 m n) :
    monomialPolynomialHypersurfaceGlobalFamily_chart312 R m n p i =
      monomialPolynomialContainmentChartHypersurfaceFamily310 R m n p i :=
  Subtype.ext (monomialPolynomialHypersurfaceGlobalFamily_chartWholeIdeal312 R m n p i)

end PfaffianDescent
end
