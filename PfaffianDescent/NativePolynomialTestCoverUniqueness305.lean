import PfaffianDescent.NativeSchemeCoverIsoCharts300
import PfaffianDescent.NativePolynomialScalarScheme300
import PfaffianDescent.FiniteFlatHilbertTestPoints195
import PfaffianDescent.WholeIdealOpenCoverUniqueness

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

variable {A : Type u} [CommRing A] (m : ℕ) (U : (Spec (.of A)).AffineOpenCover.{u})
variable [∀ i, Algebra A (U.X i)]
variable (hf : ∀ i, U.f i = Spec.map (CommRingCat.ofHom (algebraMap A (U.X i))))
include hf

/-- Actual Cartesian polynomial scalar chart above each original affine test-cover component. -/
lemma nativePolynomialTestCoverChart_isPullback305 (i : U.I₀) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A (U.X i)))))
      (nativePolynomialProjection300 (U.X i) m) (nativePolynomialProjection300 A m) (U.f i) := by
  rw [hf i]
  exact nativePolynomialScalar_isPullback300 A (U.X i) m

/-- Pull back the original test cover and replace its components by their actual polynomial spectra. -/
def nativePolynomialTestOpenCover305 :
    (Spec (.of (MvPolynomial (Fin m) A))).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300 (U.openCover.pullback₁ (nativePolynomialProjection300 A m))
    (fun i => Spec (.of (MvPolynomial (Fin m) (U.X i))))
    (fun i => (nativePolynomialTestCoverChart_isPullback305 m U hf i).isoPullback)

lemma nativePolynomialTestOpenCover_map305 (i : U.I₀) :
    (nativePolynomialTestOpenCover305 m U hf).f i =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A (U.X i)))) :=
  (nativePolynomialTestCoverChart_isPullback305 m U hf i).isoPullback_hom_fst

/-- Actual whole Hilbert points are determined by their restrictions to this constructed polynomial cover. -/
lemma nativeAffineHilbertPoint_eq_of_polynomialTestCover305 {n : ℕ}
    (P Q : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n)
    (h : ∀ i : U.I₀,
      P.val.comap
          (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A (U.X i))))) =
        Q.val.comap
          (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A (U.X i)))))) :
    P = Q := by
  apply Subtype.ext
  apply wholeIdeal_eq_of_openCover_comaps (nativePolynomialTestOpenCover305 m U hf)
  intro i
  change U.I₀ at i
  exact (congrArg P.val.comap (nativePolynomialTestOpenCover_map305 m U hf i)).trans
    ((h i).trans (congrArg Q.val.comap (nativePolynomialTestOpenCover_map305 m U hf i)).symm)

end PfaffianDescent
