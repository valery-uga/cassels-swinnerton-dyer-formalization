import PfaffianDescent.MonomialPolynomialContainmentOverlap310
import PfaffianDescent.CompatibleClosedSubschemeOpenCoverDescent

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)

/-- The original finite coefficient equations glue as entire ideals on SAME H.
No global locus, gluing datum, compatibility or containment result is supplied. -/
theorem monomialPolynomialContainmentIdeal_exists310 :
    ∃ J : (monomialCoefficientGluedScheme300 R m n).IdealSheafData,
      ∀ i : MonomialCoefficientChartIndex300 m n,
        J.comap (monomialCoefficientGluedChartMap300 R m n i) =
          monomialPolynomialContainmentChartIdealSheaf310 R m n i p := by
  obtain ⟨J, hJ⟩ := compatibleClosedSubschemes_openCover_exists_globalIdeal
    (monomialCoefficientGluedOpenCover300 R m n)
    (fun i => monomialPolynomialContainmentChartIdealSheaf310 R m n i.down p)
    (monomialPolynomialContainmentChartIdealSheaf_actualOpenCover_comap310 R m n p)
  refine ⟨J, ?_⟩
  intro i
  exact hJ (ULift.up i)

/-- The coefficient-locus ideal is constructed from the proved finite equations. -/
def monomialPolynomialContainmentIdeal310 :
    (monomialCoefficientGluedScheme300 R m n).IdealSheafData :=
  Classical.choose (monomialPolynomialContainmentIdeal_exists310 R m n p)

lemma monomialPolynomialContainmentIdeal_chart310
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialContainmentIdeal310 R m n p).comap
        (monomialCoefficientGluedChartMap300 R m n i) =
      monomialPolynomialContainmentChartIdealSheaf310 R m n i p :=
  Classical.choose_spec (monomialPolynomialContainmentIdeal_exists310 R m n p) i

/-- Actual closed polynomial-containment coefficient locus in original H. -/
def monomialPolynomialContainmentLocus310 : Scheme.{u} :=
  (monomialPolynomialContainmentIdeal310 R m n p).subscheme

def monomialPolynomialContainmentLocusInclusion310 :
    monomialPolynomialContainmentLocus310 R m n p ⟶ monomialCoefficientGluedScheme300 R m n :=
  (monomialPolynomialContainmentIdeal310 R m n p).subschemeι

lemma monomialPolynomialContainmentLocusInclusion_isClosedImmersion310 :
    IsClosedImmersion (monomialPolynomialContainmentLocusInclusion310 R m n p) := by
  change IsClosedImmersion (monomialPolynomialContainmentIdeal310 R m n p).subschemeι
  infer_instance

/-- The global closed-locus embedding kernel restricts to the literal finite
equation quotient kernel on every original coefficient chart. -/
lemma monomialPolynomialContainmentLocusInclusion_chartKernel310
    (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialContainmentLocusInclusion310 R m n p).ker.comap
        (monomialCoefficientGluedChartMap300 R m n i) =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)))).ker :=
  (congrArg (fun J => J.comap (monomialCoefficientGluedChartMap300 R m n i))
    (monomialPolynomialContainmentIdeal310 R m n p).ker_subschemeι).trans
      (monomialPolynomialContainmentIdeal_chart310 R m n p i)

end PfaffianDescent
end
