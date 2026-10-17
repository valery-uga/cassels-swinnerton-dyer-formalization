import PfaffianDescent.MonomialPolynomialContainmentLocus310
import PfaffianDescent.MonomialCoefficientGlobalUniversalFamily300
import PfaffianDescent.NativeHypersurfaceFamily297

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- Exact entire polynomial ideal on the original finite-equation coefficient quotient. -/
def monomialPolynomialContainmentChartWholeIdeal310
    (i : MonomialCoefficientChartIndex300 m n) :
    MonomialWholeIdealChart287
      (A := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) i.monomials :=
  polynomialContainmentWholeChart297 i.monomials i.zeroIndex
    (monomialUniversalCoefficientPoint310 R m n i)
    (MvPolynomial.map
      (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p)

/-- The same original polynomial belongs to the entire specialized ideal;
containment is a consequence of the finite equations, not a new hypothesis. -/
lemma monomialPolynomialContainmentChartWholeIdeal_contains310
    (i : MonomialCoefficientChartIndex300 m n) :
    MvPolynomial.map
        (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p ∈
      (monomialPolynomialContainmentChartWholeIdeal310 R m n p i).val := by
  have h := polynomialContainmentWholeChart_contains297 i.monomials i.zeroIndex
    (monomialUniversalCoefficientPoint310 R m n i)
    (MvPolynomial.map
      (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p)
  change MvPolynomial.map
      (Ideal.Quotient.mkₐ R (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)).toRingHom
      (MvPolynomial.map
        (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p) ∈
    (monomialPolynomialContainmentChartWholeIdeal310 R m n p i).val at h
  rw [nativePolynomialCoefficientMap_ground310] at h
  exact h

/-- Genuine finite-flat degree-n family inside the original polynomial
hypersurface on each closed coefficient quotient, with basis derived internally. -/
def monomialPolynomialContainmentChartHypersurfaceFamily310
    (i : MonomialCoefficientChartIndex300 m n) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom
        (R := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
        (S := MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})
        (algebraMap (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
          (MvPolynomial (Fin m) (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) ⧸
            Ideal.span {MvPolynomial.map
              (algebraMap R (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)) p})))) n :=
  affineHypersurfaceWholeQuotientHilbertPoint297
    (monomialPolynomialContainmentChartWholeIdeal310 R m n p i).val
    (monomialWholeIdealChartBasis287 i.monomials
      (monomialPolynomialContainmentChartWholeIdeal310 R m n p i)) _
    (monomialPolynomialContainmentChartWholeIdeal_contains310 R m n p i)

/-- The same universal affine ambient after native base change to the
constructed closed coefficient locus. -/
def monomialPolynomialContainmentAmbient310 : Scheme.{u} :=
  pullback (monomialCoefficientAmbientToH300 R m n)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)

def monomialPolynomialContainmentAmbientToLocus310 :
    monomialPolynomialContainmentAmbient310 R m n p ⟶
      monomialPolynomialContainmentLocus310 R m n p :=
  pullback.snd _ _

/-- Actual global degree-n finite-flat embedded family over the constructed
closed coefficient locus, formed by native universal base change. -/
def monomialPolynomialContainmentRestrictedUniversalFamily310 :
    FiniteFlatHilbertPoint195 (monomialPolynomialContainmentAmbientToLocus310 R m n p) n :=
  finiteFlatHilbertBaseChange195
    (pullback.fst (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p))
    (monomialPolynomialContainmentAmbientToLocus310 R m n p)
    (monomialCoefficientAmbientToH300 R m n)
    (monomialPolynomialContainmentLocusInclusion310 R m n p)
    (IsPullback.of_hasPullback (monomialCoefficientAmbientToH300 R m n)
      (monomialPolynomialContainmentLocusInclusion310 R m n p)) n
    (monomialCoefficientGlobalUniversalFamily300 R m n)

/-- Restriction retains exactly the entire original global universal ideal. -/
lemma monomialPolynomialContainmentRestrictedUniversalFamily_wholeIdeal310 :
    (monomialPolynomialContainmentRestrictedUniversalFamily310 R m n p).val =
      (monomialCoefficientUniversalWholeIdeal300 R m n).comap
        (pullback.fst (monomialCoefficientAmbientToH300 R m n)
          (monomialPolynomialContainmentLocusInclusion310 R m n p)) := rfl

end PfaffianDescent
end
